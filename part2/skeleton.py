import ast
import argparse
import z3

class LoopConstraint():
    def __init__(self, FOR_node):
        self.var = FOR_node.target.id
        self.lower = ast.unparse(FOR_node.iter.args[0])
        self.upper = ast.unparse(FOR_node.iter.args[1])
    
    def __str__(self):
        return f"for {self.var} in range({self.lower}, {self.upper})"

class AssignmentExpression():
    def __init__(self):
        self.write_index = None
        self.read_index = None
    
    def __str__(self):
        return f"a[{self.write_index}] = a[{self.read_index}]"

    def append(self, element):
        if self.write_index is not None and self.read_index is not None:
            raise RuntimeError("Should only have a single assignment!")
        if self.write_index is None:
            self.write_index = element
        else:
            self.read_index = element

class ForLoopVisitor(ast.NodeVisitor):
    def __init__(self):
        self.loops = []
        self.assignment_expression = AssignmentExpression()

    def __str__(self):
        loops = "\n".join("  " * i + str(loop) for (i, loop) in enumerate(self.loops))
        return loops + "\n" + str(self.assignment_expression)

    def visit_For(self, node):
        self.loops.append(LoopConstraint(node))
        self.generic_visit(node)
    
    def visit_Subscript(self, node):
        self.assignment_expression.append(ast.unparse(node.slice))
        self.generic_visit(node)


# Helper function to convert expressions -> Z3
def parse_expr(node, z3_vars):
    if isinstance(node, ast.Num): 
        return z3.IntVal(node.n)
    elif isinstance(node, ast.Name):
        return z3_vars[node.id]
    elif isinstance(node, ast.BinOp):
        left = parse_expr(node.left, z3_vars)
        right = parse_expr(node.right, z3_vars)
        if isinstance(node.op, ast.Add):
            return left + right
        elif isinstance(node.op, ast.Sub):
            return left - right
        elif isinstance(node.op, ast.Mult):
            return left * right
    else:
        raise Exception(f"Unhandled expression type: {type(node)}")



# Given a python file, return an AST using the python ast module.
def get_ast_from_file(fname):
    f = open(fname, 'r')
    s = f.read()
    f.close()
    module_ast = ast.parse(s)
    body_ast = module_ast.body[0]    
    return body_ast


# Check if an ast node is a for loop
def is_FOR_node(node):
    return str(node.__class__) == "<class '_ast.For'>"

# Top level function. Given a python file name, it parses the file,
# and analyzes it to determine if the top level for loop can be done
# in parallel.
def analyze_file(fname):
    ast_tree = get_ast_from_file(fname)
    visitor = ForLoopVisitor()
    visitor.visit(ast_tree)
    
    solver = z3.Solver()
    z3_vars = {}
    
    # Create Z3 variables for loop constraints
    for loop in visitor.loops:
        loop_var = z3.Int(loop.var)
        z3_vars[loop.var] = loop_var
        lower_bound = parse_expr(ast.parse(loop.lower).body[0].value, z3_vars)
        upper_bound = parse_expr(ast.parse(loop.upper).body[0].value, z3_vars)
        solver.add(loop_var >= lower_bound, loop_var < upper_bound)

    # Distinct constraint for outermost loop variable to allow parallelization of outer loop(enforce distinctness of outer loop indices)
    outermost_loop_vars = [z3_vars[loop.var] for loop in visitor.loops[:1]]
    solver.add(z3.Distinct(outermost_loop_vars))

    # Translate assignment expressions into Z3 expressions
    write_index = parse_expr(ast.parse(visitor.assignment_expression.write_index).body[0].value, z3_vars)
    read_index = parse_expr(ast.parse(visitor.assignment_expression.read_index).body[0].value, z3_vars)

    # Check for write-write conflicts. If the constraints are satisfied, we have a conflict
    solver.push()
    solver.add(write_index == write_index)
    ww_conflict = solver.check() == z3.sat
    solver.pop()

    # Check for read-write conflicts. If the constraints are satisfied, we have a conflict. 
    solver.push()
    solver.add(write_index == read_index)
    rw_conflict = solver.check() == z3.sat
    solver.pop()
    
    return ww_conflict, rw_conflict


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('pythonfile', help='The python file to be analyzed')
    args = parser.parse_args()
    ww_conflict, rw_conflict = analyze_file(args.pythonfile)
    print("Does the code have a write-write conflict? ", ww_conflict)
    print("Does the code have a read-write conflict? ", rw_conflict)
