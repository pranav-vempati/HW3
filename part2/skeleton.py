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

class AssignmentExpression(list):
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
#
# It returns True if it is safe to do the top loop in parallel,
# otherwise it returns False.
def analyze_file(fname):
    ast = get_ast_from_file(fname)

    # Suggested steps:
    # 1. Get loop constraints (variables and bounds)
    # 2. Get expressions for read_index and write_index
    visitor = ForLoopVisitor()
    visitor.visit(ast)
    print(visitor)
    
    # 3. Create constraints and check them
    # TODO: Use Z3 to create and solve constraints

    # Set these variables to True if there is a write-write (ww)
    # conflict or a read-write (rw) conflict
    ww_conflict = False
    rw_conflict = False
    
    return ww_conflict, rw_conflict
    
if __name__ == '__main__':
    parser = argparse.ArgumentParser()   
    parser.add_argument('pythonfile', help ='The python file to be analyzed') 
    args = parser.parse_args()
    # ww_conflict, rw_conflict = analyze_file(f"/Users/tjbanghart/HW3/part2/test_cases/6.py")
    ww_conflict, rw_conflict = analyze_file(args.pythonfile)
    print("Does the code have a write-write conflict? ", ww_conflict)
    print("Does the code have a read-write conflict?  ", rw_conflict)
