import copy


__all__ = ["Rule", "Axiom", "TheoremProver"]


def flatten(seq):
    """Flatten the sequence."""
    return [item for sublist in seq for item in sublist]


def find(f, seq):
    """Return first item in sequence where f(item) == True."""
    for item in seq:
        if f(item):
            return item


def remove_duplicate(f, seq):
    """Return the sequence without the duplicates as specified by f(item_1, item_2) == True."""
    return_list = []
    for item in seq:
        for r_item in return_list:
            if f(item, r_item):
                break
        else:
            return_list.append(item)
    return return_list


def merge_theorem_lists(theorem_0, theorem_1):
    """Merge two theorem lists."""
    return remove_duplicate(lambda t_1, t_2: t_1.result == t_2.result, theorem_0 + theorem_1)


class Rule:
    """The rule class holds a rule that can be used.

    :param name: The name of the rule.
    :param func: The function that defines the rule.
    """

    def __init__(self, name, func):
        self.name = name
        self.func = func

    def __repr__(self):
        return self.name


class Theorem:
    """A theorem consists of an axiom, a result and a list of rules to go from the axiom to the result.

    :param axiom: The axiom of the theorem.
    :param rules: The rules to go from the axiom to the theorem.
    :param result: The result of the theorem.
    """

    def __init__(self, axiom, rules, result):
        self.axiom = axiom
        self.rules = rules
        self.result = result

    def apply_rule(self, theorem_prover, rule):
        """Apply a rule to the theorem.

        :param theorem_prover: The theorem prover.
        :param rule: The rule that needs to be applied to the theorem.
        :return: A list of newly created theorems that follow from the theorem and the given rule.
        """
        return [Theorem(self.axiom, self.rules + [rule], rule.func(self.result, theorem_prover))]

    def apply_rules(self, theorem_prover, rules):
        """Apply a list of rules to the theorem.

        :param theorem_prover: The theorem prover.
        :param rules: The rules that need to be applied to the theorem.
        :return: A list of newly created theorems that follow from the theorem and the given rules.
        """
        # Initialize the theorem list
        theorem_list = []
        # For each rule
        for rule in rules:
            theorem_list += self.apply_rule(theorem_prover, rule)
        # Return the newly created theorems
        return theorem_list


class Axiom(Theorem):
    """This class represents an axiom which is theorem that is assumed to be correct.

    :param axiom: The axiom.
    """

    def __init__(self, axiom):
        super().__init__([axiom], [], axiom)


class TheoremProver:
    """This class proves theorems.

    :param axioms: The axioms the theorem prover starts with.
    :param rules: The rules the theorem prover may use.
    """

    def __init__(self, axioms, rules):
        self.axioms = axioms
        self.rules = rules

    def find_proof(self, target, max_depth=100):
        """Find the proof for a given target.

        :param target: The target that needs to be reached, from the axioms and the rules in the theorem prover.
        :param max_depth: After the maximum depth is reached the theorem prover will halt its search.
        :return: Returns the theorem with the corresponding rules if the proof is found else it will return None.
        """
        found_theorems = copy.deepcopy(self.axioms)
        depth = 0

        while True:
            if target in [theorem.result for theorem in found_theorems]:
                return find(lambda t: t.result == target, found_theorems)
            elif depth > max_depth:
                return None
            else:
                theorems = flatten([theorem.apply_rules(self, self.rules) for theorem in found_theorems])
                found_results_set = {theorem.result for theorem in found_theorems}
                theorems_results_set = {theorem.result for theorem in theorems}
                if found_results_set | theorems_results_set == found_results_set:
                    return None
                else:
                    found_theorems = merge_theorem_lists(found_theorems, theorems)
                    depth += 1
