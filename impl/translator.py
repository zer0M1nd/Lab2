from z3 import *

verbose = False


def DeclareVar(sort, name):
    if sort == "Int":
        return Int(name)
    if sort == 'Bool':
        return Bool(name)


def getSort(sort):
    if sort == "Int":
        return IntSort()
    if sort == "Bool":
        return BoolSort()
    if type(sort) == list and sort[0] == "BitVec":  # sygus 1.0 format: (BitVec 64)
        return BitVecSort(sort[1][1])
    if type(sort) == list and sort[0] == "_" and sort[1] == "BitVec":  # sygus 2.0 format: (_ BitVec 64)
        return BitVecSort(sort[2][1])
    print("Error: unknown sort", sort)
    assert False


def constToString(sort, value):
    # print(sort, value)
    if sort == "Int" or sort == "Bool":
        return str(value)
    if type(sort) == list and sort[0] == "_":
        sort = sort[1:]
    if type(sort) == list and sort[0] == "BitVec":
        l = sort[1][1]
        assert l % 4 == 0
        v = hex(value)[2:]
        v = "#x" + "0" * (l // 4 - len(v)) + v
        return v
    print("Error: unknown sort", sort)
    assert False


def toString(Expr, Bracket=True, ForceBracket=False):
    if type(Expr) == str:
        return Expr
    if type(Expr) == tuple:
        return constToString(Expr[0], Expr[1])
    if Expr==None:
        return None
    if Expr[0] == "BitVec":
        return "(_ BitVec " + str(Expr[1][1]) + ")"
    subexpr = []
    for expr in Expr:
        if type(expr) == list:
            subexpr.append(toString(expr, ForceBracket=ForceBracket))
        elif type(expr) == tuple:
            subexpr.append(constToString(expr[0], expr[1]))
        else:
            subexpr.append(expr)

    if not Bracket:
        # print subexpr
        return "%s" % (' '.join(subexpr))
    # Avoid Redundant Brackets
    if ForceBracket:
        return "(%s)" % (' '.join(subexpr))
    if len(subexpr) == 1:
        return "%s" % (' '.join(subexpr))
    else:
        return "(%s)" % (' '.join(subexpr))

class SynFunction:
        def __init__(self, SynFunExpr):
            self.name = SynFunExpr[1]
            # TODO: arg and ret sort
            self.argList = SynFunExpr[2]
            self.retSort = SynFunExpr[3]
            self.Sorts = []
            for expr in self.argList:
                self.Sorts.append(getSort(expr[1]))
            self.Sorts.append(getSort(self.retSort))
            self.targetFunction = Function('__TARGET_FUNCTION__', *(self.Sorts))

class Checker:
        def __init__(self, VarTable, synFunction, Constraints, AuxFuns,TransTable,SynFunExpr):

            self.VarTable = VarTable
            self.synFunction = synFunction
            self.TransTable = TransTable
            self.Constraints = Constraints
            self.AuxFuns = AuxFuns            
            self.SynFunExpr = SynFunExpr
            self.CounterExamples = []
            self.solver = Solver()

        def check(self, funcDefStr):
            self.solver.push()

            spec_smt2 = self.AuxFuns + [funcDefStr]
            for constraint in self.Constraints:
                spec_smt2.append('(assert %s)' % (toString(constraint[1:])))
            spec_smt2 = '\n'.join(spec_smt2)
            spec = parse_smt2_string(spec_smt2, decls=dict(self.VarTable))
            spec = And(spec)
            for i in self.CounterExamples:
                if i.eval(Not(spec)):
                    return i

            self.solver.add(Not(spec))
            if verbose:
                print("spec:", spec)
            res = self.solver.check()
            if res == unsat:
                self.solver.pop()
                return None
            else:
                model = self.solver.model()
                self.solver.pop()
                self.CounterExamples.append(model)
                return model


def ReadQuery(bmExpr):
    SynFunExpr = []
    VarDecMap = {}
    Constraints = []
    FunDefMap = {}
    AuxFuns = []    
    TransTable = {}
    VarDecList = []

    for expr in bmExpr:
        if len(expr) == 0:
            continue
        elif expr[0] == 'synth-fun':
            SynFunExpr = expr
        elif expr[0] == 'declare-var':
            VarDecMap[expr[1]] = expr
            VarDecList.append(expr[1])
        elif expr[0] == 'constraint':
            Constraints.append(expr)
        elif expr[0] == 'define-fun':
            FunDefMap[expr[1]] = expr
            AuxFuns.append(toString(expr, ForceBracket=True))

    argument = SynFunExpr[2]    

    if len(VarDecList) == len(argument):
        for i in range(len(VarDecList)):
            var = VarDecList[i]
            arg = argument[i][0]
            TransTable[var] = arg

    if verbose:
        print(SynFunExpr)
        print(VarDecMap)
        print(FunDefMap)
        print(Constraints)

    VarTable = {}
    # Declare Var
    for var in VarDecMap:
        VarTable[var] = DeclareVar(VarDecMap[var][2], var)

    # Declare Target Function
    

    synFunction = SynFunction(SynFunExpr)


    checker = Checker(VarTable, synFunction, Constraints, AuxFuns, TransTable, SynFunExpr)
    return checker
