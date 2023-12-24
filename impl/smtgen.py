from typing import *

import z3

import translator


def sort_tostring(sort) -> str:
    if sort == z3.IntSort():
        return "i"
    elif sort == z3.BoolSort():
        return "b"
    elif isinstance(sort, z3.z3.BitVecSortRef):
        return "v" + str(sort.size())
    else:
        raise ValueError("What sort?")


def stupid_select(lst, idx):
    cur = lst[-1]

    for i in range(len(lst) - 2, -1, -1):
        cur = z3.If(idx == i, lst[i], cur)

    return cur


class SMTGen:

    def __init__(self,
                 constraints: List,
                 syn_func: translator.SynFunction,
                 func_defs: List[str],
                 var_defs: Dict[str, z3.ArithRef],
                 production_type: Dict[str, Any],
                 productions: Dict[str, List]):
        self.constraints: List = list(x[1] for x in constraints)
        self.syn_func = syn_func
        self.func_defs = func_defs
        self.var_defs = var_defs

        self.production_type: Dict[str, z3.SortRef] = {x: translator.getSort(y) for x, y in production_type.items()}
        self.productions = productions

        self.current_outputs: Dict[z3.SortRef, List] = dict()
        self.current_outputs_z3array: Dict[z3.SortRef, z3.ArrayRef] = dict()

        self.new_vars: Dict[str, z3.ExprRef] = dict()

        self.added_assertions: List[z3.ExprRef] = list()
        self.added_assertions_str: List[str] = list()

        self.final_output_varname = ""

        self.samples = []
        self.not_available = False

        self.func_argname = ""

        self.model = None

        self.idx_gen = {}

    def add_var(self, sort, name) -> z3.ExprRef:
        """
        declare a z3 var and add to track in self.new_vars
        """
        if name in self.new_vars:
            # print("REP NAME:", name)
            return self.new_vars[name]
        if sort == z3.IntSort():
            r = z3.Int(name)
        elif sort == z3.BoolSort():
            r = z3.Bool(name)
        elif isinstance(sort, z3.z3.BitVecSortRef):
            r = z3.BitVec(name, sort.size())
        else:
            raise ValueError("What sort?")
        self.new_vars[name] = r
        return r

    def replace_input(self, expr: Any, outer_typename: str, outer_id: int, added_vars: List[Tuple], sample_id: int):
        if isinstance(expr, list):  # function
            l1 = list()
            for i, e in enumerate(expr):
                if i == 0:
                    l1.append(e)
                else:
                    l1.append(self.replace_input(e, outer_typename, outer_id, added_vars, sample_id))
            return l1
        elif isinstance(expr, tuple):  # constant
            return expr
        elif isinstance(expr, str):  # variable
            if expr == self.func_argname:
                return self.samples[sample_id][0]
            if expr not in self.productions:
                return expr
            inner_id = len(added_vars)
            my_type = self.production_type[expr]

            ivname = "i_{}_{:d}_{:d}_{:d}".format(outer_typename, outer_id, inner_id, sample_id)

            input_var = self.add_var(my_type, ivname)
            select_var = self.add_var(z3.IntSort(),
                                      "s_{}_{:d}_{:d}".format(outer_typename, outer_id, inner_id))
            added_vars.append((input_var, select_var))

            return ivname
        else:
            print("What the fuck?")
            print(expr)

    def gen_component(self, left: str, right: Any, idx: int, final, sample_id: int):
        leftsort = self.production_type[left]

        sname = sort_tostring(leftsort)

        # idx = len(self.current_outputs[leftsort])
        self.idx_gen[idx] = (left, right)

        oname = "output" if final else "o_{}_{}".format(sname, str(idx))
        oname = oname + "_" + str(sample_id)
        output = self.add_var(leftsort, oname)

        print("Handling", right)

        added_vars: List[Tuple[z3.ExprRef, z3.ArithRef]] = list()
        replaced_right = self.replace_input(right, sname, idx, added_vars, sample_id)

        for iv, sv in added_vars:
            tp = iv.sort()
            self.added_assertions.append(iv == stupid_select(self.current_outputs[tp], sv))

            # z3.Select()

            # self.added_assertions.append(z3.And(sv >= 0, sv < len(self.current_outputs[tp])))

        self.added_assertions_str.append("(assert (= {} {}))".format(oname, translator.toString(replaced_right)))

        self.current_outputs[leftsort].append(output)
        # self.current_outputs_z3array[leftsort] = z3.Store(self.current_outputs_z3array[leftsort], idx, output)

    def gen_all_components(self, rounds: int = 1):
        for leftsort in self.production_type.values():
            if leftsort not in self.current_outputs:
                self.current_outputs[leftsort] = list()
        #        self.current_outputs_z3array[leftsort] = z3.Array("arr_" + sort_tostring(leftsort), z3.IntSort(),
        #                                                          leftsort)

        for i in range(len(self.samples)):

            idx = 0

            for rd in range(rounds):
                for k, v in list(self.productions.items())[::-1]:
                    for r in v:
                        self.gen_component(k, r, idx, False, i)
                        idx += 1

            # Add an extra gen for
            for k, v in list(self.productions.items())[::-1]:
                for r in v:
                    if k == "My-Start-Symbol":
                        self.gen_component(k, r, idx, True, i)
                        idx += 1
                        break

    def get_samples(self):

        all_constraints_are_samples = True

        samples = []

        for l in self.constraints:
            l1 = l
            if not isinstance(l1, list) or l1[0] != '=':
                all_constraints_are_samples = False
                break
            if not (isinstance(l1[1], list) and l1[1][0] == self.syn_func.name and isinstance(l1[1][1], tuple)):
                all_constraints_are_samples = False
                break
            if not isinstance(l1[2], tuple):
                all_constraints_are_samples = False
                break
            samples.append((l1[1][1], l1[2]))

        if len(self.var_defs) == 0 and all_constraints_are_samples:
            self.samples = samples
        else:
            self.not_available = True

    def solve(self):

        # assert len(self.var_defs) == 0
        print(self.new_vars)

        solver = z3.Solver()

        if any(isinstance(x.sort(), z3.BitVecSortRef) for x in self.new_vars.values()):
            pass  # set logic?
        else:
            pass

        smt2_lst = self.func_defs + self.added_assertions_str

        smt2_str = "\n".join(smt2_lst)

        print(smt2_str)

        spec = z3.parse_smt2_string(smt2_str, decls=dict(self.var_defs | self.new_vars))

        solver.add(spec)
        solver.add(self.added_assertions)

        for i in range(len(self.samples)):
            solver.add(self.new_vars["output_" + str(i)] == self.samples[i][1][1])

        res = solver.check()
        print(res)

        if res == z3.sat:
            self.model = solver.model()
        else:
            self.model = None

        print(self.model)

    def walk_result(self, expr: Any, visits: Dict):
        pass

    def expand_result(self, idx):
        pass

    def get_result(self):
        pass

    def run(self):
        self.get_samples()

        if self.not_available:
            return False

        for arg in self.syn_func.argList:
            name, type = tuple(arg)
            self.func_argname = name

        self.gen_all_components()

        # print(self.new_vars)
        # print(self.added_assertions)
        # print(self.added_assertions_str)

        self.solve()

        return True
