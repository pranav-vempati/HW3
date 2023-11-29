import ast
import argparse
import z3
import collections

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

class Z3Thread():
    def __init__(self, visitor, thread_id):
        self.thread_id = thread_id
        self.visitor = visitor
        self.z3_vars = collections.OrderedDict()
        for loop in visitor.loops:
            self.z3_vars[loop.var] = z3.Int(f'{loop.var}_{thread_id}')
    
    def outer_loop_var(self):
        return list(self.z3_vars.values())[0]

    def add_all_loop_constraints(self, solver):
        for loop in self.visitor.loops:
            loop_var = self.z3_vars[loop.var]
            solver.add(loop_var >= self._calculate_lower_bound(loop), loop_var < self._calculate_upper_bound(loop))
    
    def write_index(self):
        """Translate write index into Z3 expressions"""
        return self._parse_expr(ast.parse(self.visitor.assignment_expression.write_index).body[0].value, self.z3_vars)
    
    def read_index(self):
        """Translate read index into Z3 expressions"""
        return self._parse_expr(ast.parse(self.visitor.assignment_expression.read_index).body[0].value, self.z3_vars)
    
    def _calculate_lower_bound(self, loop):
        return self._parse_expr(ast.parse(loop.lower).body[0].value, self.z3_vars)
    
    def _calculate_upper_bound(self, loop):
        return self._parse_expr(ast.parse(loop.upper).body[0].value, self.z3_vars)

    # Helper function to convert expressions -> Z3
    def _parse_expr(self, node, z3_vars):
        if isinstance(node, ast.Num): 
            return z3.IntVal(node.n)
        elif isinstance(node, ast.Name):
            return z3_vars[node.id]
        elif isinstance(node, ast.BinOp):
            left = self._parse_expr(node.left, z3_vars)
            right = self._parse_expr(node.right, z3_vars)
            if isinstance(node.op, ast.Add):
                return left + right
            elif isinstance(node.op, ast.Sub):
                return left - right
            elif isinstance(node.op, ast.Mult):
                return left * right
            elif isinstance(node.op, ast.Div):
                return left / right
            elif isinstance(node.op, ast.Mod):
                return left % right
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

# Top level function. Given a python file name, it parses the file,
# and analyzes it to determine if the top level for loop can be done
# in parallel.
def analyze_file(fname):
    ast_tree = get_ast_from_file(fname)
    visitor = ForLoopVisitor()
    visitor.visit(ast_tree)
    #print(visitor)
    
    solver = z3.Solver()

    # Create Z3 variables for loop constraints
    (thread1, thread2) = [Z3Thread(visitor, 0), Z3Thread(visitor, 1)]

    # Distinct constraint for outermost loop variable to allow parallelization of outer loop(enforce distinctness of outer loop indices)
    solver.add(thread1.outer_loop_var() != thread2.outer_loop_var())

    # Distinct constraint for outermost loop variable to allow parallelization of outer loop(enforce distinctness of outer loop indices)
    thread1.add_all_loop_constraints(solver)
    thread2.add_all_loop_constraints(solver)

    # Check for write-write conflicts. If the constraints are satisfied, we have a conflict
    solver.push()
    solver.add(thread1.write_index() == thread2.write_index())
    ww_conflict = solver.check() == z3.sat
    solver.pop()

    # Check for read-write conflicts. If the constraints are satisfied, we have a conflict. 
    solver.push()
    solver.add(thread1.write_index() == thread2.read_index())
    rw_conflict = solver.check() == z3.sat
    solver.pop()
    
    return ww_conflict, rw_conflict

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('pythonfile', help='The python file to be analyzed')
    args = parser.parse_args()
    # ww_conflict, rw_conflict = analyze_file(f"/Users/tjbanghart/HW3/part2/test_cases/2.py")
    ww_conflict, rw_conflict = analyze_file(args.pythonfile)
    print("Does the code have a write-write conflict? ", ww_conflict)
    print("Does the code have a read-write conflict? ", rw_conflict)
