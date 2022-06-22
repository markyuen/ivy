import logic as ll
import ivy_actions as ia
import ivy_module as im
import ivy_logic as il
import ivy_logic_utils as ilu
from collections import defaultdict
from ivy_union_find import *
from johnson import simple_cycles


def derived_relations_rewrite(strat_map, arcs, print_arcs=False, print_drs=False):
    def pra(s):
        if print_arcs:
            print(s)

    def prd(s):
        if print_drs:
            print(s)

    nodes = set()
    pra("nodes = [")
    for x, y in strat_map.iteritems():
        z = find(y)
        nodes.add(z)
        if isinstance(x, tuple):
            pra("\t({}  |  {}) : {} -> {}".format(x[0], x[1], y, z))
        else:
            pra("\t{} : {} -> {}".format(x, y, z))
    pra("]\n")

    nodes = sorted(nodes, key=lambda x: x.id)
    pra("UFNodes = [")
    [pra("\t{}: {}".format(x.id, get_node_sort(strat_map, x))) for x in nodes]
    pra("]\n")

    g = {u: set() for u in nodes}
    arc_fmlas = defaultdict(set)
    pra("arcs = [")
    for arc in arcs:
        u = find(arc[0])
        v = find(arc[1])
        g[u].add(v)
        arc_fmlas[v].add(tuple(arc[2:]))
        pra("\t{}:{} -> {}:{}".format(u, get_node_sort(strat_map, arc[0]), v, get_node_sort(strat_map, arc[1])))
        pra("\t{}".format("  |  ".join(str(x) for x in arc[2:])))
    pra("]\n")

    cycles = sorted(list(simple_cycles(g)), key=lambda x: len(x))
    pra("UF cycles: [")
    for c in cycles:
        s = []
        for n in c:
            s.append("{}:{}".format(n.id, get_node_sort(strat_map, n)))
        pra("\t{}".format(" -> ".join(s + [s[0]])))
    pra("]\n")

    cycled_nodes = set(flatten(cycles))
    fmlas_to_check = {}
    for fs in arc_fmlas:
        if fs in cycled_nodes:
            pra("to {}:{} = [".format(fs.id, get_node_sort(strat_map, fs)))
            for f in arc_fmlas[fs]:
                rel = f[0]
                line = f[1].line
                fmla = f[2]
                close_fmla = f[3]
                pra("\t{}  |  line {}  |  {}".format(rel, line, fmla))
                if close_fmla not in fmlas_to_check:
                    fmlas_to_check[close_fmla] = (line, set())
                fmlas_to_check[close_fmla][1].add(get_node_sort(strat_map, fs).name)
            pra("]")

    prd("\nderived relations = [")
    sr = static_relations()
    ier = init_empty_relations()
    for f, (line, terminals) in fmlas_to_check.items():
        prd("\n\tline {}  |  {}  |  {}".format(line, terminals, f))
        derived_relation(f, set(), sr, ier, terminals, print_drs)
    prd("]")


def derived_relation(fmla, univs, sr, ier, terminals, print_drs):
    if il.is_forall(fmla):
        univs = univs.union(set([v for v in fmla.variables]))
    else:
        # if no univs are used, then clear the univs set
        if not [v for v in ilu.variables_ast(fmla) if v in univs]:
            univs = set()
    if il.is_exists(fmla):
        exs = set([v for v in fmla.variables])
        # TODO this can be relaxed -- only the candidate phi needs to be qf
        if il.is_qf(fmla.body) and univs:
            derived_relation_aux(fmla.body, univs, exs, sr, ier, terminals, print_drs)
    for f in fmla.args:
        derived_relation(f, univs, sr, ier, terminals, print_drs)


def derived_relation_aux(arg_fmla, arg_univs, arg_exs, sr, ier, terminals, print_drs):
    def prd(s):
        if print_drs:
            print(s)

    literals = set(literals_ast(arg_fmla))
    positive_literals = set([f for f in literals if not isinstance(f, ll.Not)])
    static_literals = set([f for f in literals if literal_func(f) in sr])
    tcf = top_conj_fmlas(arg_fmla)
    # the derived relation candidate must be positive, cannot be an axiom, must be a top-level conj, must initially be empty
    potential_ps = [l for l in positive_literals - static_literals if l in tcf and literal_func(l) in ier]
    # phi can only contain static relations
    base_phis = [f for f in tcf if all(l in static_literals for l in literals_ast(f))]
    potential_phis = [reduce(lambda x, y: ll.And(x, y), l) for l in permute(base_phis)]
    # generate all possible quantifiers
    # There can be multiple quantifier choices here because ex variables under p
    # can be universal. That being said, ex cannot be empty. A greedy approach to
    # this is to remove as many ex vars as possible (i.e., make the ex set as large
    # as possible). As an optimization, we can de-prioritize psis which transfer
    # sorts to univs that still need to be maintained in the formula (for other
    # relations). We might look to discard these entirely, but there might be a
    # chance that with the derived relation the equivalence class of that instance
    # actually becomes stratified. We can also discard psis with ex vars that do
    # not address the cycles they contribute to (by comaparing the ex vars to
    # the terminals of the formula's arcs) -- this might be particularly common
    # when the negative version of an invariant invokes a cycle.
    # To gen quantifiers:
    #   - all ex vars under phi must appear in p as well (?) -- not enforced currently
    #   - can phi contain local vars -> psi univs? -- not allowed currently
    #   - psi_univs contains all univs under phi and p and any local vars under p
    #   - psi_exs begins with all other vars, reduces down till only a single var
    # TODO discard other useless options, such as those that coincide with an edge from an axiom
    potential_psis = []

    def add_psi(univs, us, ps, exs, phi, p):
        psi_univs = list(univs.union(us).union(ps))
        psi_exs = exs - us
        flag1 = psi_univs  # a derived relation is formable
        flag2 = len(terminals - set([v.sort.name for v in psi_exs])) < len(terminals)  # addresses a cycle
        if flag1 and flag2:
            # generate arity mapping for update code
            psi_umap = {v: i for i, v in enumerate(psi_univs)}
            p_map = {v: i for i, v in enumerate(p.terms)}
            # map phi [i -> (origin, j)]:
            # index i of phi is taken from index j from origin p or psi
            gen_phi_map = []
            for v in ilu.variables_ast(phi):
                if v in psi_umap:
                    gen_phi_map.append(("PSI", psi_umap[v]))
                else:
                    gen_phi_map.append(("P", p_map[v]))
            # map dr update [i -> j]:
            # index i of dr is updated using index j of p (i.e., U_i = p_j)
            gen_dr_update_map = [p_map.get(v, None) for v in psi_univs]
            potential_psis.append((psi_univs, psi_exs, phi, p, gen_phi_map, gen_dr_update_map))

    for p in potential_ps:
        p_vars = set([v for v in ilu.variables_ast(p)])
        p_univs = set([v for v in p_vars if v in arg_univs])
        p_exs = set([v for v in p_vars if v in arg_exs])
        p_locals = set([c for c in ilu.constants_ast(p)])
        # consider a vacuous phi
        # moving no vars
        add_psi(p_univs, set(), p_locals, p_exs, ll.And(), p)
        # moving n-1 ex vars
        ex_to_univ = [set(x) for x in permute(p_exs) if len(x) < len(p_exs)]
        for us in ex_to_univ:
            add_psi(p_univs, us, p_locals, p_exs, ll.And(), p)
        # non-empty phis
        for phi in potential_phis:
            phi_vars = set([v for v in ilu.variables_ast(phi)])
            phi_univs = set([v for v in phi_vars if v in arg_univs])
            phi_exs = set([v for v in phi_vars if v in arg_exs])
            phi_locals = set([c for c in ilu.constants_ast(phi)])
            all_univs = phi_univs.union(p_univs)
            all_exs = phi_exs.union(p_exs)
            # moving no vars
            add_psi(all_univs, set(), p_locals, all_exs, phi, p)
            # moving n-1 ex vars
            ex_to_univ = [set(x) for x in permute(all_exs) if len(x) < len(all_exs)]
            for us in ex_to_univ:
                add_psi(all_univs, us, p_locals, all_exs, phi, p)
    # generate update code for insertion of a single element
    # An update on p would alter some (potentiallly none) univ vars and all ex vars.
    # Given p(a, b, c) := true, we allow updates of p(a, b, c) := true (i.e., a single
    # update), where a, b, and c are not quantified. Given psi univ vars of A and B, we
    # would update psi like so: psi(A, B) := psi(A, B) | (phi & A = a & B = b) -- in
    # other words, we only update the relevant derived relation. phi may depend on A, B,
    # and/or c -- that is fine, just inline c when needed (the univ vars would already
    # be properly placed). Note that under certain conditions multiple updates can be
    # allowed. Specifically, if an ex var under p and psi and NOT under phi is mass
    # updated (i.e., applied over the sort), then this does not change the update code --
    # intuitively, this derived relation is still coherent since that var falls under
    # an ex quant, so an instance still exists. Additionally, a univ var can also be
    # mass updated -- this is the same as just applying the update across all instances
    # of the derived relation. The only case where vars under p CANNOT be mass updated
    # is when an ex var under p also appears under psi and phi.
    # To gen update:
    #   - check that the lhs of the stmt is in psi
    #   - check that the rhs of the update is `true`
    #   - extract all vars under p
    #   - verify that no capitalized ex vars under p appear in phi (through arity location of the var)
    #   - gen `psi(X) := psi(X) | (phi & X1 = x1 & X2 = x2 ...)` for each ex quant x under p (do not include vars not in psi univs)
    # init and example of single update
    for i, psi in enumerate(potential_psis):
        DERIVED_RELATION_NAME = "dr"
        univs, exs, phi, p, gen_phi_map, gen_dr_update_map = psi
        # init: dr(X) := false
        j = 65
        init_vars = []
        for _ in range(len(univs)):  # TODO what if more than 26 vars...
            init_vars.append(chr(j))
            j += 1
        dr_sort = ll.FunctionSort(*([u.sort for u in univs] + [ll.Boolean]))
        declaration_ast = ll.Const(DERIVED_RELATION_NAME, dr_sort)
        dr_terms = [ll.Const(init_vars[k], univs[k].sort) for k in range(len(univs))]
        dr_ast = ll.Apply(declaration_ast, *dr_terms)
        init_ast = ia.AssignAction(dr_ast, ll.Or())
        # single update example: p(x) := true
        # gen sample AssignAction stmt
        aa = gen_single_update_stmt(exs, phi, p)
        # parse assignment
        parsed_p_name, parsed_terms = parse_single_update_stmt(aa)
        # gen update code
        assert parsed_p_name in set(p)  # TODO later
        update_conds = []
        # add phi condition
        if phi == ll.And():
            update_conds.append(ll.And())
        else:
            # complete phi map by mapping to actual names now
            phi_map = []
            for origin, idx in gen_phi_map:
                if origin == "PSI":
                    phi_map.append(dr_terms[idx].name)
                else:
                    assert origin == "P"
                    phi_map.append(parsed_terms[idx].name)
            update_conds.append(gen_phi(phi, phi_map))
        # add conditional univ updates
        for j, idx in enumerate(gen_dr_update_map):
            if idx is not None:
                update_conds.append(ll.Eq(dr_terms[j], parsed_terms[idx]))
        update_conds_ast = reduce(lambda x, y: ll.And(x, y), update_conds)
        update_rhs_ast = ll.Or(dr_ast, update_conds_ast)
        update_code_ast = ia.AssignAction(dr_ast, update_rhs_ast)
        update = (aa, update_code_ast)
        # gen repr inv
        ri_ex_vars = []
        ri_p_vars = []
        j = 65 + len(univs)
        for v in p.terms:
            if v in exs:
                ri_ex_vars.append(ll.Var(chr(j), v.sort))
                ri_p_vars.append(ll.Var(chr(j), v.sort))
                j += 1
            else:
                ri_p_vars.append(dr_terms[univs.index(v)])
        # add phi
        ri_phi_ast = ll.And()
        if phi != ll.And():
            phi_map = []
            for origin, idx in gen_phi_map:
                if origin == "PSI":
                    phi_map.append(dr_terms[idx].name)
                else:
                    assert origin == "P"
                    phi_map.append(ri_p_vars[idx].name)
            ri_phi_ast = gen_phi(phi, phi_map)
        ri_p_ast = ll.Apply(p.func, *ri_p_vars)
        ri_rhs = ll.And(ri_phi_ast, ri_p_ast)
        if ri_ex_vars:
            ri_rhs = ll.Exists(ri_ex_vars, ri_rhs)
        repr_inv_ast = ll.Iff(dr_ast, ri_rhs)
        # gen univ repr inv
        univ_repr_inv_ast = ll.Implies(ll.And(ri_phi_ast, ri_p_ast), dr_ast) if ri_ex_vars else repr_inv_ast
        potential_psis[i] = (
        univs, exs, phi, p, gen_phi_map, gen_dr_update_map, declaration_ast, init_ast, update, repr_inv_ast,
        univ_repr_inv_ast)
    # for example
    # print im.module.actions["aaa"] #ivy1.6
    # print im.module.actions["bbb"] #ivy1.7
    # print type(im.module.actions["bbb"].args[1].args[2].args[1].args[0].terms[3])
    if potential_psis:
        prd("\tuniv vars: " + str([str(v) for v in arg_univs]))
        prd("\tex vars: " + str([str(v) for v in arg_exs]))
        prd("\texistential formula: " + str(arg_fmla))
        prd("\tliterals: " + str([str(l) for l in literals]))
        prd("\tpositive literals: " + str([str(l) for l in positive_literals]))
        prd("\tstatic literals: " + str([str(l) for l in static_literals]))
        prd("\ttop-level conjs: " + str([str(l) for l in tcf]))
        prd("\tpotential ps: " + str([str(l) for l in potential_ps]))
        prd("\tpotential phis: " + str([str(l) for l in potential_phis]))
        prd("\tpotential psis: [")
        for l in potential_psis:
            prd("\t\tunivs: {}  |  exs: {}".format(", ".join(map(lambda x: str(x), l[0])),
                                                   ", ".join(map(lambda x: str(x), l[1]))))
            prd("\t\tphi: {}  |  p: {}".format(l[2], l[3]))
            prd("\t\tphi_mp: {}  |  dr_up_mp: {}".format(l[4], l[5]))
            prd("\t\tdeclaration: {}  |  init: {}".format(l[6], l[7]))
            prd("\t\tupdate: {} -> {}".format(l[8][0], l[8][1]))
            prd("\t\trepr inv: {}".format(l[9]))
            prd("\t\tuniv repr inv: {}".format(l[10]))
            prd("") if l != potential_psis[-1] else None
        prd("\t]")
        import ivy_printer as ip
        # im.module.actions["bbb"].args.append(aa)
        # il.sig.symbols[DERIVED_RELATION_NAME] = declaration_ast
        # ip.print_module(im.module)

    # TODO support removal of elements


def gen_phi(fmla, mp):
    def aux(fmla):
        if isinstance(fmla, ll.And):
            l, r = fmla.args
            lhs = aux(l)
            rhs = aux(r)
            return ll.And(lhs, rhs)
        if isinstance(fmla, ll.Or):
            l, r = fmla.args
            lhs = aux(l)
            rhs = aux(r)
            return ll.Or(lhs, rhs)
        if isinstance(fmla, ll.Eq):
            lhs = aux(fmla.t1)
            rhs = aux(fmla.t2)
            return ll.Eq(lhs, rhs)
        if isinstance(fmla, ll.Not):
            body = fmla.args[0]
            return ll.Not(aux(body))
        if isinstance(fmla, ll.Apply):
            nt = []
            for t in fmla.terms:
                name = mp[aux.ctr]
                if name.isupper():
                    nt.append(ll.Var(name, t.sort))
                else:
                    nt.append(ll.Const(name, t.sort))
                aux.ctr += 1
            return ll.Apply(fmla.func, *nt)
        if isinstance(fmla, ll.Var) or isinstance(fmla, ll.Const):
            name = mp[aux.ctr]
            if name.isupper():
                return ll.Var(name, fmla.sort)
            else:
                return ll.Const(name, fmla.sort)
        assert False, type(fmla)

    aux.ctr = 0
    return aux(fmla)


def gen_single_update_stmt(exs, phi, p):
    j = 97
    aa_terms = []
    for k in range(len(p.terms)):
        aa_terms.append(ll.Const(chr(j), p.terms[k].sort))
        j += 1
    aa = ia.AssignAction(ll.Apply(p.func, *aa_terms), ll.And())
    p_terms_is_ex = [t in exs for t in p.terms]
    for j, t in enumerate(aa.args[0].terms):
        is_mass_update = t.name[0].isupper()
        is_ex_in_p = p_terms_is_ex[j]
        is_in_phi = p.terms[j] in [v for v in ilu.variables_ast(phi)]
        if is_mass_update and is_ex_in_p and is_in_phi:
            raise Exception("Update not allowed: {}  |  {}: {}".format(aa, j, t))
    return aa


def parse_single_update_stmt(aa):
    assert isinstance(aa, ia.AssignAction)  # must be assignment
    assert aa.args[1] == ll.And()  # rhs must be `true`
    return aa.args[0][0], tuple(aa.args[0][1:])


def permute(it):
    from itertools import combinations
    return sum([map(list, combinations(it, i)) for i in range(1, len(it) + 1)], [])


def top_conj_fmlas(fmla):
    conjs = set()

    def aux(fmla):
        if isinstance(fmla, ll.And):
            # And is left assoc in ivy1.6
            for f in fmla.args[1:]:
                if isinstance(f, ll.And):
                    # but there may be unnecessary brackets on the right surrounding an And
                    aux(f)
                else:
                    conjs.add(f)
            aux(fmla.args[0])
        else:
            conjs.add(fmla)

    aux(fmla)
    return conjs


def init_empty_relations():
    empty_rels = set()
    # ivy1.6
    for ldf in im.module.labeled_inits:
        if not ldf.temporal:
            fmla = ldf.formula
            if isinstance(fmla, ll.Not):
                body = fmla.body
                assert isinstance(body, ll.Apply)
                if all(v.name.isupper() for v in body.terms):
                    empty_rels.add(body.func.name)
            else:
                assert isinstance(fmla, ll.Apply)
                empty_rels.discard(fmla.func.name)
    # ivy1.7
    symbols = il.sig.symbols
    for seq in im.module.initial_actions:
        for action in seq.args:
            if isinstance(action, ia.AssignAction):
                l, r = action.args
                assert l.func.name in symbols
                const = symbols[l.func.name]
                assert isinstance(const, ll.Const)
                fs = const.sort
                assert isinstance(fs, ll.FunctionSort)
                flag1 = fs[-1] == ll.Boolean  # must be a relation
                flag2 = r == ll.Or()  # rhs must be `false`
                flag3 = all(v.name.isupper() for v in l.terms)  # must be for the entire relation
                if flag1 and flag2 and flag3:
                    empty_rels.add(l.func.name)
                elif flag1 and flag2 and l.func.name in empty_rels:
                    # we can relax flag3 if the rhs is just `false` and all three
                    # conditions were previously already satisfied
                    pass
                else:
                    # if any of the above fail, then rm from set, since multiple
                    # assignments to the relation can exist and a later one can
                    # overwrite a prior empty initialization
                    empty_rels.discard(l.func.name)
    return empty_rels


def static_relations():
    static_rels = set("=")
    for ldf in im.module.labeled_axioms:
        if not ldf.temporal:
            for f in literals_ast(ldf.formula):
                static_rels.add(literal_func(f))
    return static_rels


def literals_ast(ast):
    if is_literal(ast):
        yield ast
        if isinstance(ast, ll.Not):
            return
    for arg in ast.args:
        for x in literals_ast(arg):
            yield x


def is_literal(term):
    flag1 = isinstance(term, ll.Not) and is_literal(term.body)
    flag2 = isinstance(term, ll.Apply)
    flag3 = isinstance(term, ll.Eq) and is_literal(term.t1) and is_literal(term.t2)
    return flag1 or flag2 or flag3


def literal_func(lit):
    if isinstance(lit, ll.Not):
        return literal_func(lit.body)
    else:
        if isinstance(lit, ll.Eq):
            return "="
        else:
            return lit.func.name


def flatten(l):
    return [x for xs in l for x in xs]


def get_node_sort(strat_map, n):  # from ivy_fragment
    for t, m in strat_map.iteritems():
        if m is n:
            if isinstance(t, tuple):
                return t[0].sort.dom[t[1]]
            return t.sort
    assert False
