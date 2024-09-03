#!/usr/bin/env python3

import collections

import peano


TheoremStatement = collections.namedtuple('TheoremStatement', ['name', 'statement', 'premises'])


class ProblemSet:
    '''
    A problem set has a list of thereom statements to solve on a background theory,
    and keeps track of which theorems have been proved and can be used next.
    '''
    def __init__(self,
                 theory: str,
                 initial_library: list[str],
                 statements: list[TheoremStatement]):
        self._theory = theory
        self._statements = collections.OrderedDict([(s.name, s) for s in statements])
        self._initial_library = initial_library
        self._solved = set()
        self._discovered_library = set()

    def problem_names(self) -> list[str]:
        return list(self._statements.keys())

    def solved(self) -> list[str]:
        'Returns the solved problems, respecting the problem set order.'
        return [k for k in self._statements if k in self._solved]

    def __len__(self):
        return len(self._statements)

    def initialize_problem(self, name):
        statement = self._statements[name]

        theory = [self._theory]

        for name in self._discovered_library.union(set(statement.premises)):
            if name in self._statements:
                theory.append(f'{name} : {self._statements[name].statement}.')

        return peano.PyProofState('\n'.join(theory),
                                  self._initial_library + list(self._discovered_library) + statement.premises,
                                  statement.statement)

    def initialize_external_problem(self, statement: str):
        '''Creates a fresh state for a statement that is outside the problemset.

        The actions will include the problemset's background theory and the discovered library.'''
        theory = [self._theory]

        for name in self._discovered_library:
            theory.append(f'{name} : {self._statements[name].statement}.')

        return peano.PyProofState('\n'.join(theory),
                                  self._initial_library + list(self._discovered_library),
                                  statement)

    def mark_as_solved(self, problem_name, add_to_library=True):
        self._solved.add(problem_name)

        if add_to_library:
            self._discovered_library.add(problem_name)

    def is_solved(self, problem_name: str) -> bool:
        return problem_name in self._solved

    def cumulative_pass_rate(self) -> float:
        return len(self._solved) / len(self._statements)


def load_lean_library_logic_problemset():
    logic_theory = """
and : [prop -> prop -> prop].

and_elim_l : [('p : prop) -> ('q : prop) -> (and 'p 'q) -> 'p].
#forward and_elim_l ('po : (and 'p 'q)).
and_elim_r : [('p : prop) -> ('q : prop) -> (and 'p 'q) -> 'q].
#forward and_elim_r ('po : (and 'p 'q)).
and_intro : [('p : prop) -> ('q : prop) -> 'p -> 'q -> (and 'p 'q)].
#backward and_intro infer infer subgoal subgoal.

or : [prop -> prop -> prop].

or_l : [('p : prop) -> ('q : prop) -> 'p -> (or 'p 'q)].
#backward or_l infer infer subgoal.

or_r : [('p : prop) -> ('q : prop) -> 'q -> (or 'p 'q)].
#backward or_r infer infer subgoal.

or_elim : [('p : prop) -> ('q : prop) -> (or 'p 'q) ->
           ('r : prop) -> ['p -> 'r] -> ['q -> 'r]
           -> 'r].
#backward or_elim infer infer infer infer subgoal subgoal.

false : prop.
false_elim : [('p : prop) -> false -> 'p].
#backward false_elim infer infer.

not : [prop -> prop] = (lambda ('p0 : prop) ['p0 -> false]).

iff : [prop -> prop -> prop] = (lambda ('p1 : prop, 'p2 : prop) (and ['p1 -> 'p2] ['p2 -> 'p1])).
    """

    lean_lib_problems = [
        TheoremStatement("mt", "[('p : prop) -> ('q : prop) -> ['p -> 'q] -> (not 'q) -> (not 'p)]", []),
        TheoremStatement("non_contradictory", "[('p : prop) -> 'p -> (not (not 'p))]", []),
        TheoremStatement("not_false", "(not false)", []),
        TheoremStatement("and_swap", "[('p : prop) -> ('q : prop) -> (and 'p 'q) -> (and 'q 'p)]", []),
        TheoremStatement("non_contradictory_em", "[('p : prop) -> (not (not (or 'p (not 'p))))]", []),
        TheoremStatement("or_swap", "[('p : prop) -> ('q : prop) -> (or 'p 'q) -> (or 'q 'p)]", []),
        TheoremStatement("iff_elim_left", "[('p : prop) -> ('q : prop) -> (iff 'p 'q) -> ['p -> 'q]]", []),
        TheoremStatement("iff_elim_right", "[('p : prop) -> ('q : prop) -> (iff 'p 'q) -> ['q -> 'p]]", []),
        TheoremStatement("iff_refl", "[('p : prop) -> (iff 'p 'p)]", []),
        TheoremStatement("iff_symm", "[('p : prop) -> ('q : prop) -> (iff 'p 'q) -> (iff 'q 'p)]", []),
        TheoremStatement("iff_trans", "[('p : prop) -> ('q : prop) -> ('r : prop) -> (iff 'p 'q) -> (iff 'q 'r) -> (iff 'p 'r)]", []),
        TheoremStatement("not_of_iff_false", "[('p : prop) -> (iff 'p false) -> (not 'p)]", []),
        TheoremStatement("imp_congr", "[('a : prop) -> ('b : prop) -> ('c : prop) -> ('d : prop) -> (iff 'a 'c) -> (iff 'b 'd) -> (iff ['a -> 'b] ['c -> 'd])]", []),
        TheoremStatement("and_imp", "[('a : prop) -> ('b : prop) -> ('c : prop) -> ('d : prop) -> ['a -> 'c] -> ['b -> 'd] -> (and 'a 'b) -> (and 'c 'd)]", []),
        TheoremStatement("and_comm", "[('a : prop) -> ('b : prop) -> (iff (and 'a 'b) (and 'b 'a))]", []),
        TheoremStatement("and_assoc", "[('a : prop) -> ('b : prop) -> ('c : prop) -> (and 'a (and 'b 'c)) -> (and (and 'a 'b) 'c)]", []),
        TheoremStatement("and_iff_left", "[('a : prop) -> ('b : prop) -> 'b -> (iff (and 'a 'b) 'a)]", []),
        TheoremStatement("and_iff_right", "[('a : prop) -> ('b : prop) -> 'a -> (iff (and 'a 'b) 'b)]", []),
        TheoremStatement("and_false", "[('a : prop) -> (iff (and 'a false) false)]", []),
        TheoremStatement("false_and", "[('a : prop) -> (iff (and false 'a) false)]", []),
        TheoremStatement("and_self", "[('a : prop) -> (iff (and 'a 'a) 'a)]", []),
    ]

    return ProblemSet(
        logic_theory,
        ['and_elim_l', 'and_elim_r', 'and_intro', 'or_l', 'or_r', 'or_elim', 'false_elim'],
        lean_lib_problems
    )


def load_natural_number_game_problemset():
    nng_theory = """
= : [('t : type) -> 't -> 't -> prop].

nat : type.
false : prop.

z : nat.
s : [nat -> nat].

+ : [nat -> nat -> nat].
* : [nat -> nat -> nat].
^ : [nat -> nat -> nat].

#forward s.
#forward +.

/* Defining axioms for addition */
+_z : [('n : nat) -> (= (+ 'n z) 'n)].
+_s : [('n : nat) -> ('m : nat) -> (= (+ 'n (s 'm)) (s (+ 'n 'm)))].
#forward +_z ((+ 'n z) : nat).
#forward +_s ((+ 'n (s 'm)) : nat).

/* Defining axioms for multiplication */
*_z : [('n : nat) -> (= (* 'n z) z)].
*_s : [('n : nat) -> ('m : nat) -> (= (* 'n (s 'm)) (+ 'n (* 'n 'm)))].
#forward *_z ((* 'n z) : nat).
#forward *_s ((* 'n (s 'm)) : nat).

/* Defining axioms for exponentiation */
^_z : [('n : nat) -> (= (^ 'n z) (s z))].
^_s : [('n : nat) -> ('m : nat) -> (= (^ 'n (s 'm)) (* 'n (^ 'n 'm)))].
#forward ^_z ((^ 'n z) : nat).
#forward ^_s ((^ 'n (s 'm)) : nat).

/* Natural number induction */
nat_ind : [('p : [nat -> prop]) -> ('p z) -> [('n : nat) -> ('p 'n) -> ('p (s 'n))] -> [('n : nat) -> ('p 'n)]].
#backward nat_ind infer subgoal subgoal.

#forward succ_inj ((= (s 'a) (s 'b)) : 't).
succ_inj : [('a : nat) -> ('b : nat) -> (= (s 'a) (s 'b)) -> (= 'a 'b)].

exists : [('t : type) -> ('p : ['t -> prop]) -> prop].
ex_intro : [('t : type) -> ('p : ['t -> prop]) -> ('x : 't) -> ('p 'x) -> (exists 't 'p)].
ex_wit : [('t : type) -> ('p : ['t -> prop]) -> (exists 't 'p) -> 't].
ex_elim : [('t : type) -> ('p : ['t -> prop]) -> ('e : (exists 't 'p)) -> ('p (ex_wit 't 'p 'e))].

#backward ex_intro infer infer infer subgoal.
#forward ex_wit.
#forward ex_elim ('e : (exists 't 'p)).

leq : [nat -> nat -> prop] = (lambda ('a : nat, 'b : nat)
                                     (exists nat (lambda ('c : nat) (= (+ 'a 'c) 'b)))).

#forward rewrite.
#forward eq_refl.
#forward eq_symm ((= 'a 'b) : 't).

and : [prop -> prop -> prop].

and_elim_l : [('p : prop) -> ('q : prop) -> (and 'p 'q) -> 'p].
#forward and_elim_l ('po : (and 'p 'q)).
and_elim_r : [('p : prop) -> ('q : prop) -> (and 'p 'q) -> 'q].
#forward and_elim_r ('po : (and 'p 'q)).
and_intro : [('p : prop) -> ('q : prop) -> 'p -> 'q -> (and 'p 'q)].
#backward and_intro infer infer subgoal subgoal.

or : [prop -> prop -> prop].

or_l : [('p : prop) -> ('q : prop) -> 'p -> (or 'p 'q)].
#backward or_l infer infer subgoal.

or_r : [('p : prop) -> ('q : prop) -> 'q -> (or 'p 'q)].
#backward or_r infer infer subgoal.

or_elim : [('p : prop) -> ('q : prop) -> (or 'p 'q) ->
           ('r : prop) -> ['p -> 'r] -> ['q -> 'r]
           -> 'r].
#backward or_elim infer infer infer infer subgoal subgoal.

false_elim : [('p : prop) -> false -> 'p].
#backward false_elim infer infer.

not : [prop -> prop] = (lambda ('p0 : prop) ['p0 -> false]).

iff : [prop -> prop -> prop] = (lambda ('p1 : prop, 'p2 : prop) (and ['p1 -> 'p2] ['p2 -> 'p1])).

zero_ne_succ : [('a : nat) -> (not (= z (s 'a)))].
#forward zero_ne_succ.

empty : type.

#forward a_zero_add ((+ z 'n) : nat).
#forward a_succ_add ((+ (s 'a) 'b) : nat).
#forward a_add_assoc ((+ (+ 'a 'b) 'c) : nat).
/* #forward a_add_assoc ((+ 'a (+ 'b 'c)) : nat). */
#forward a_add_comm ((+ 'a 'b) : nat).
#forward a_succ_eq_add_one. /* ((s 'n) : nat). */
/* #forward a_succ_eq_add_one ((+ 'n (s z)) : nat). */
#forward a_add_right_comm ((+ (+ 'a 'b) 'c) : nat).

#forward m_zero_mul ((* z 'm) : nat).
#forward m_mul_one ((* 'm (s z)) : nat).
#forward m_one_mul ((* (s z) 'm) : nat).
#forward m_mul_add ((* 't (+ 'a 'b)) : nat).
#forward m_mul_assoc ((* (* 'a 'b) 'c) : nat).
#forward m_mul_comm ((* 'a 'b) : nat).


#forward succ_eq_succ_of_eq ('_ : (= 'a 'b)) ((s 'a) : nat) ((s 'b) : nat).
    """

    n2 = '(s (s z))'
    n7 = '(s (s (s (s (s (s (s z)))))))'

    nng_problems = [
        TheoremStatement("t_example1", "[('x : nat) -> ('y : nat) -> ('z : nat) -> (= (+ (* 'x 'y) 'z) (+ (* 'x 'y) 'z))]", []),
        TheoremStatement("t_example2", f"[('x : nat) -> ('y : nat) -> (= 'y (+ 'x {n7})) -> (= (* {n2} 'y) (* {n2} (+ 'x {n7})))]", []),
        TheoremStatement("t_example3", "[('a : nat) -> ('b : nat) -> (= (s 'a) 'b) -> (= (s (s 'a)) (s 'b))]", []),
        TheoremStatement("t_add_succ_zero", "[('a : nat) -> (= (+ 'a (s z)) (s 'a))]", []),
        TheoremStatement("a_zero_add", "[('n : nat) -> (= (+ z 'n) 'n)]", []),
        TheoremStatement("a_add_assoc", "[('a : nat) -> ('b : nat) -> ('c : nat) -> (= (+ (+ 'a 'b) 'c) (+ 'a (+ 'b 'c)))]", []),
        TheoremStatement("a_succ_add", "[('a : nat) -> ('b : nat) -> (= (+ (s 'a) 'b) (s (+ 'a 'b)))]", []),
        TheoremStatement("a_add_comm", "[('a : nat) -> ('b : nat) -> (= (+ 'a 'b) (+ 'b 'a))]", ['a_zero_add', 'a_succ_add']),
        TheoremStatement("a_succ_eq_add_one", "[('n : nat) -> (= (s 'n) (+ 'n (s z)))]", []),
        TheoremStatement("a_add_right_comm", "[('a : nat) -> ('b : nat) -> ('c : nat) -> (= (+ (+ 'a 'b) 'c) (+ (+ 'a 'c) 'b))]", ['a_add_assoc', 'a_add_comm']),
    ]
    remaining_problems = [
        TheoremStatement("m_zero_mul", "[('m : nat) -> (= (* z 'm) z)]", ['*_z', '*_s']),
        TheoremStatement("m_mul_one", "[('m : nat) -> (= (* 'm (s z)) 'm)]", ['*_z', '*_s']),
        TheoremStatement("m_one_mul", "[('m : nat) -> (= (* (s z) 'm) 'm)]", ['*_z', '*_s', 'a_add_comm', 'a_succ_eq_add_one']),
        TheoremStatement("m_mul_add", "[('t : nat) -> ('a : nat) -> ('b : nat) -> (= (* 't (+ 'a 'b)) (+ (* 't 'a) (* 't 'b)))]", ['*_z', '*_s', 'a_add_comm', 'a_add_assoc']),
        TheoremStatement("m_mul_assoc", "[('a : nat) -> ('b : nat) -> ('c : nat) -> (= (* (* 'a 'b) 'c) (* 'a (* 'b 'c)))]", ['*_z', '*_s', 'm_mul_add']),
        TheoremStatement("m_succ_mul", "[('a : nat) -> ('b : nat) -> (= (* (s 'a) 'b) (+ (* 'a 'b) 'b))]", ['*_z', '*_s', 't_add_succ_zero', 'a_add_assoc', 'a_add_comm']),
        TheoremStatement("m_add_mul", "[('a : nat) -> ('b : nat) -> ('t : nat) -> (= (* (+ 'a 'b) 't) (+ (* 'a 't) (* 'b 't)))]", ['*_z', '*_s', 'a_add_comm', 'a_add_assoc']),
        TheoremStatement("m_mul_comm", "[('a : nat) -> ('b : nat) -> (= (* 'a 'b) (* 'b 'a))]", ['*_z', '*_s', 'm_zero_mul', 'm_succ_mul', 'a_add_comm']),
        TheoremStatement("m_mul_left_comm", "[('a : nat) -> ('b : nat) -> ('c : nat) -> (= (* 'a (* 'b 'c)) (* 'b (* 'a 'c)))]", ['*_z', '*_s', 'm_mul_assoc', 'm_mul_comm']),

        TheoremStatement("p_zero_pow_zero", "(= (^ z z) (s z))", ['^_z']),
        TheoremStatement("p_zero_pow_succ", "[('m : nat) -> (= (^ z (s 'm)) z)]", ['^_z', '^_s', '*_z', '*_s', 'm_zero_mul']),
        TheoremStatement("p_pow_one", "[('a : nat) -> (= (^ 'a (s z)) 'a)]", ['^_z', '^_s', 'p_zero_pow_succ', '*_s', '*_z']),
        TheoremStatement("p_one_pow", "[('m : nat) -> (= (^ (s z) 'm) (s z))]", ['^_z', '^_s', 'p_zero_pow_succ', '*_s', '*_z']),
        TheoremStatement("p_pow_add", "[('a : nat) -> ('m : nat) -> ('n : nat) -> (= (^ 'a (+ 'm 'n)) (* (^ 'a 'm) (^ 'a 'n)))]", ['^_z', '^_s', 'p_zero_pow_succ', '*_s', '*_z', 'p_pow_one']),
        TheoremStatement("p_mul_pow", "[('a : nat) -> ('b : nat) -> ('n : nat) -> (= (^ (* 'a 'b) 'n) (* (^ 'a 'n) (^ 'b 'n)))]", ['^_z', '^_s', 'p_zero_pow_succ', '*_s', '*_z', 'p_pow_one', 'p_pow_add']),
        TheoremStatement("p_pow_pow", "[('a : nat) -> ('m : nat) -> ('n : nat) -> (= (^ (^ 'a 'm) 'n) (^ 'a (* 'm 'n)))]", ['^_z', '^_s', 'p_zero_pow_succ', '*_s', '*_z', 'p_pow_one', 'p_pow_add', 'p_mul_pow']),
        TheoremStatement("p_add_squared", "[('a : nat) -> ('b : nat) -> (= (^ (+ 'a 'b) (s (s z))) (+ (+ (^ 'a (s (s z))) (^ 'b (s (s z)))) (* (s (s z)) (* 'a 'b))))]", ['^_z', '^_s', 'p_zero_pow_succ', '*_s', '*_z', 'p_pow_one', 'p_pow_add']),

        TheoremStatement("f_example1", "[('P : type) -> ('Q : type) -> ('p : 'P) -> ('h : ['P -> 'Q]) -> 'Q]", []),
        TheoremStatement("f_example2", "[nat -> nat]", []),
        TheoremStatement("f_example3", "[('P : type) -> ('Q : type) -> ('R : type) -> ('S : type) -> ('T : type) -> ('U : type) -> ('p : 'P) -> ('h : ['P -> 'Q]) -> ('i : ['Q -> 'R]) -> ('j : ['Q -> 'T]) -> ('k : ['S -> 'T]) -> ('l : ['T -> 'U]) -> 'U]", []),
        TheoremStatement("f_example4", "[('P : type) -> ('Q : type) -> ('R : type) -> ('S : type) -> ('T : type) -> ('U : type) -> ('p : 'P) -> ('h : ['P -> 'Q]) -> ('i : ['Q -> 'R]) -> ('j : ['Q -> 'T]) -> ('k : ['S -> 'T]) -> ('l : ['T -> 'U]) -> 'U]", []),
        TheoremStatement("f_example5", "[('P : type) -> ('Q : type) -> ('p : 'P) -> ('q : 'Q) -> 'P]", []),
        TheoremStatement("f_example6", "[('P : type) -> ('Q : type) -> ('R : type) -> ('f : ['P -> ['Q -> 'R]]) -> ('g : ['P -> 'Q]) -> ('p : 'P) -> 'R]", []),
        TheoremStatement("f_example7", "[('P : type) -> ('Q : type) -> ('F : type) -> ('f : ['P -> 'Q]) -> ('g : ['Q -> 'F]) -> ('p : 'P) -> 'F]", []),
        TheoremStatement("f_example8", "[('P : type) -> ('Q : type) -> ('f : ['P -> 'Q]) -> ('g : ['Q -> empty]) -> ('p : 'P) -> empty]", []),
        TheoremStatement("f_example9", "[('A : type) -> ('B : type) -> ('C : type) -> ('D : type) -> ('E : type) -> ('F : type) -> ('G : type) -> ('H : type) -> ('I : type) -> ('J : type) -> ('K : type) -> ('L : type) -> ('f1 : ['A -> 'B]) -> ('f2 : ['B -> 'E]) -> ('f3 : ['E -> 'D]) -> ('f4 : ['D -> 'A]) -> ('f5 : ['E -> 'F]) -> ('f6 : ['F -> 'C]) -> ('f7 : ['B -> 'C]) -> ('f8 : ['F -> 'G]) -> ('f9 : ['G -> 'J]) -> ('f10 : ['I -> 'J]) -> ('f11 : ['J -> 'I]) -> ('f12 : ['I -> 'H]) -> ('f13 : ['E -> 'H]) -> ('f14 : ['H -> 'K]) -> ('f15 : ['I -> 'L]) -> ('a : 'A) -> 'L]", []),

        TheoremStatement("p_example1", "[('P : prop) -> ('Q : prop) -> ('p : 'P) -> ('h : ['P -> 'Q]) -> 'Q]", []),
        TheoremStatement("p_imp_self", "[('P : prop) -> ('p : 'P) -> 'P]", []),
        TheoremStatement("p_maze", "[('P : prop) -> ('Q : prop) -> ('R : prop) -> ('S : prop) -> ('T : prop) -> ('U : prop) -> ('p : 'P) -> ('h : ['P -> 'Q]) -> ('i : ['Q -> 'R]) -> ('j : ['Q -> 'T]) -> ('k : ['S -> 'T]) -> ('l : ['T -> 'U]) -> 'U]", []),
        TheoremStatement("p_example2", "[('P : prop) -> ('Q : prop) -> 'P -> ['Q -> 'P] ]", []),
        TheoremStatement("p_example3", "[('P : prop) -> ('Q : prop) -> ('R : prop) -> ['P -> ['Q -> 'R]] -> [['P -> 'Q] -> ['P -> 'R]]]", []),
        TheoremStatement("imp_trans", "[('P : prop) -> ('Q : prop) -> ('R : prop) -> ['P -> 'Q] -> ['Q -> 'R] -> ['P -> 'R]]", []),
        TheoremStatement("contrapositive", "[('P : prop) -> ('Q : prop) -> ['P -> 'Q] -> [(not 'Q) -> (not 'P)]]", []),
        TheoremStatement("pw_example5", "[('A : prop) -> ('B : prop) -> ('C : prop) -> ('D : prop) -> ('E : prop) -> ('F : prop) -> ('G : prop) -> ('H : prop) -> ('I : prop) -> ('J : prop) -> ('K : prop) -> ('L : prop) -> ('f1 : ['A -> 'B]) -> ('f2 : ['B -> 'E]) -> ('f3 : ['E -> 'D]) -> ('f4 : ['D -> 'A]) -> ('f5 : ['E -> 'F]) -> ('f6 : ['F -> 'C]) -> ('f7 : ['B -> 'C]) -> ('f8 : ['F -> 'G]) -> ('f9 : ['G -> 'J]) -> ('f10 : ['I -> 'J]) -> ('f11 : ['J -> 'I]) -> ('f12 : ['I -> 'H]) -> ('f13 : ['E -> 'H]) -> ('f14 : ['H -> 'K]) -> ('f15 : ['I -> 'L]) -> 'A -> 'L]", []),
        TheoremStatement("apw_example1", "[('P : prop) -> ('Q : prop) -> 'P -> 'Q -> (and 'P 'Q)]", ['and_intro']),
        TheoremStatement("and_symm", "[('P : prop) -> ('Q : prop) -> (and 'P 'Q) -> (and 'Q 'P)]", ['and_intro', 'and_elim_r', 'and_elim_l']),
        TheoremStatement("and_trans", "[('P : prop) -> ('Q : prop) -> ('R : prop) -> (and 'P 'Q) -> (and 'Q 'R) -> (and 'P 'R)]", ['and_intro', 'and_elim_r', 'and_elim_l']),

        TheoremStatement("iff_trans", "[('P : prop) -> ('Q : prop) -> ('R : prop) -> (iff 'P 'Q) -> (iff 'Q 'R) -> (iff 'P 'R)]", ['and_intro', 'and_elim_r', 'and_elim_l']),
        TheoremStatement("apw_example2", "[('P : prop) -> ('Q : prop) -> ('q : 'Q) -> (or 'P 'Q)]", ['or_l', 'or_r', 'or_elim']),
        TheoremStatement("or_symm", "[('P : prop) -> ('Q : prop) -> (or 'P 'Q) -> (or 'Q 'P)]", ['or_l', 'or_r', 'or_elim']),
        TheoremStatement("and_or_distrib_left", "[('P : prop) -> ('Q : prop) -> ('R : prop) -> (iff (and 'P (or 'Q 'R)) (or (and 'P 'Q) (and 'P 'R)))]", ['and_intro', 'and_elim_r', 'and_elim_l', 'or_l', 'or_r', 'or_elim']),
        TheoremStatement("contra", "[('P : prop) -> ('Q : prop) -> (and 'P (not 'P)) -> 'Q]", ['and_intro', 'and_elim_r', 'and_elim_l', 'or_l', 'or_r', 'or_elim', 'false_elim']),
        TheoremStatement("contrapositive2", "[('P : prop) -> ('Q : prop) -> [(not 'Q) -> (not 'P)] -> ['P -> 'Q]]", []),
        TheoremStatement("succ_inj'", "[('a : nat) -> ('b : nat) -> (= (s 'a) (s 'b)) -> (= 'a 'b)]", ['succ_inj']),
        TheoremStatement("succ_succ_inj", "[('a : nat) -> ('b : nat) -> (= (s (s 'a)) (s (s 'b))) -> (= 'a 'b)]", ['succ_inj']),
        TheoremStatement("succ_eq_succ_of_eq", "[('a : nat) -> ('b : nat) -> (= 'a 'b) -> (= (s 'a) (s 'b))]", ['succ_inj']),
        TheoremStatement("succ_eq_succ_iff", "[('a : nat) -> ('b : nat) -> (iff (= (s 'a) (s 'b)) (= 'a 'b))]", ['and_intro', 'succ_inj', 'succ_eq_succ_of_eq']),

        TheoremStatement("add_right_cancel", "[('a : nat) -> ('t : nat) -> ('b : nat) -> (= (+ 'a 't) (+ 'b 't)) -> (= 'a 'b)]", ['succ_eq_succ_of_eq']),
        TheoremStatement("add_left_cancel", "[('t : nat) -> ('a : nat) -> ('b : nat) -> (= (+ 't 'a) (+ 't 'b)) -> (= 'a 'b)]", ['succ_eq_succ_of_eq', 'a_add_comm']),
        TheoremStatement("add_right_cancel_iff", "[('t : nat) -> ('a : nat) -> ('b : nat) -> (iff (= (+ 'a 't) (+ 'b 't)) (= 'a 'b))]", ['and_intro', 'add_right_cancel']),
        TheoremStatement("eq_zero_of_add_right_eq_self", "[('a : nat) -> ('b : nat) -> (= (+ 'a 'b) 'a) -> (= 'b z)]", []),

        TheoremStatement("succ_ne_zero", "[('a : nat) -> (not (= (s 'a) z))]", ['zero_ne_succ', 'false_elim']),
        TheoremStatement("add_left_eq_zero", "[('a : nat) -> ('b : nat) -> (= (+ 'a 'b) z) -> (= 'b z)]", ['succ_ne_zero', 'false_elim']),
        TheoremStatement("add_right_eq_zero", "[('a : nat) -> ('b : nat) -> (= (+ 'a 'b) z) -> (= 'a z)]", ['add_left_eq_zero', 'a_add_comm']),
        TheoremStatement("add_one_eq_succ", "[('d : nat) -> (= (+ 'd (s z)) (s 'd))]", []),
        TheoremStatement("ne_succ_self", "[('n : nat) -> (not (= 'n (s 'n)))]", ['zero_ne_succ', 'succ_inj', 'false_elim']),

        TheoremStatement("one_add_le_self", "[('x : nat) -> (leq 'x (+ (s z) 'x))]", ['ex_intro', 'a_add_comm']),
        TheoremStatement("le_refl", "[('x : nat) -> (leq 'x 'x)]", ['ex_intro']),
        TheoremStatement("le_succ", "[('a : nat) -> ('b : nat) -> (leq 'a 'b) -> (leq 'a (s 'b))]",
                         ['ex_intro', 'ex_elim', 's']),
        TheoremStatement("zero_le", "[('x : nat) -> (leq z 'x)]", ['ex_intro', 'a_zero_add']),
        TheoremStatement("le_trans", "[('x : nat) -> ('y : nat) -> ('z : nat) -> (leq 'x 'y) -> (leq 'y 'z) -> (leq 'x 'z)]",
                         ['ex_intro', 'ex_elim', '+', 'a_add_assoc']),
        TheoremStatement("succ_le_succ", "[('x : nat) -> ('y : nat) -> (leq 'x 'y) -> (leq (s 'x) (s 'y))]",
                         ['ex_intro', 'ex_elim', 'a_succ_add']),
        TheoremStatement("le_succ_self", "[('x : nat) -> (leq 'x (s 'x))]", ['s', 'ex_intro', 't_add_succ_zero']),
        TheoremStatement("le_antisymm", "[('a : nat) -> ('b : nat) -> (leq 'a 'b) -> (leq 'b 'a) -> (= 'a 'b)]",
                         ['a_add_assoc', 'ex_elim', 'eq_zero_of_add_right_eq_self', 'add_left_eq_zero']),
        TheoremStatement("le_zero", "[('a : nat) -> (leq 'a z) -> (= 'a z)]", ['ex_elim', 'add_right_eq_zero']),
        TheoremStatement("not_succ_le_self", "[('a : nat) -> (not (leq (s 'a) 'a))]", ['ex_elim', 'ex_intro', 'zero_ne_succ', 'a_succ_add', 'succ_inj', 'a_add_comm']),
        TheoremStatement("le_of_succ_le_succ", "[('a : nat) -> ('b : nat) -> (leq (s 'a) (s 'b)) -> (leq 'a 'b)]", ['ex_intro', 'ex_elim', 'succ_inj', 'a_succ_add']),

        TheoremStatement("add_le_add_right", "[('a : nat) -> ('b : nat) -> (leq 'a 'b) -> ('t : nat) -> (leq (+ 'a 't) (+ 'b 't))]", ['a_add_assoc']),
        TheoremStatement("add_le_add_left", "[('a : nat) -> ('b : nat) -> (leq 'a 'b) -> ('t : nat) -> (leq (+ 't 'a) (+ 't 'b))]", ['add_le_add_right', 'a_add_comm']),
    ]
    left_out = [
        # Advanced multiplication world.
        TheoremStatement("mul_pos", "[('a : nat) -> ('b : nat) -> (not (= 'a z)) -> (not (= 'b z)) -> (not (= (* 'a 'b) z))]", []),
        TheoremStatement("eq_zero_or_eq_zero_of_mul_eq_zero", "[('a : nat) -> ('b : nat) -> (= (* 'a 'b) z) -> (or (= 'a z) (= 'b z))]", []),
        TheoremStatement("mul_eq_zero_iff", "[('a : nat) -> ('b : nat) -> (iff (= (* 'a 'b) z) (or (= 'a z) (= 'b z)))]", []),
        TheoremStatement("mul_left_cancel", "[('a : nat) -> ('b : nat) -> ('c : nat) -> (not (= 'a z)) -> (= (* 'a 'b) (* 'a 'c)) -> (= 'b 'c)]", []),

        TheoremStatement("le_total", "[('a : nat) -> ('b : nat) -> (or (leq 'a 'b) (leq 'b 'a))]", []),

        TheoremStatement("lt_aux_one", "[('a : nat) -> ('b : nat) -> (and (leq 'a 'b) (not (leq 'b 'a))) -> (leq (s 'a) 'b)]", []),
        TheoremStatement("lt_aux_two", "[('a : nat) -> ('b : nat) -> (leq (s 'a) 'b) -> (and (leq 'a 'b) (not (leq 'b 'a)))]", []),
        TheoremStatement("lt_iff_succ_le", "[('a : nat) -> ('b : nat) -> (iff (lt 'a 'b) (leq (s 'a) 'b))]", []),
    ]

    return ProblemSet(
        nng_theory,
        ['eq_symm', 'eq_refl', 'rewrite', 'nat_ind', '+_z', '+_s'],
        nng_problems + remaining_problems,
    )


def load_problemset(problemset_id) -> ProblemSet:
    if problemset_id in ('lean-library-logic', 'logic'):
        return load_lean_library_logic_problemset()
    elif problemset_id in ('natural-number-game', 'nng'):
        return load_natural_number_game_problemset()
    raise ValueError(f'Unknown problem set {problemset_id}')
