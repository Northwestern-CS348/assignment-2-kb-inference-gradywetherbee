import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        print("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here



        # for item in fact.supports_facts:
        #     self.kb_retract(item)
        # for item in fact.supports_rules:
        #     self.kb_retract(item)

        # Case: purely asserted fact -> retracted directly so it's removed
        if type(fact) == Fact:

            if fact.asserted:
                if fact.supported_by:
                    fact.asserted = False
                    return

                else: # Fact not supported
                    for child in fact.supports_facts:
                        if not child.asserted:
                            self.kb_retract(child)

                        else:
                            child.supported_by.remove(fact)

            else: # Fact purely inferred
                for parent in fact.supported_by:
                    parent.supports_facts.remove(fact)

                for child in fact.supports_facts:
                    child.supported_by.remove(fact)
                    self.kb_retract(child)
                for child in fact.supports_rules:
                    child.supported_by.remove(fact)

            self.facts.remove(fact)
        return













class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        ####################################################
        # Student code goes here
        # Find matches for the first element of the left hand side list
        binding = match(fact.statement, rule.lhs[0])

        if binding:
            if len(rule.lhs) > 1:
                # Create an empty list to go through the rest of the left hand side
                rest = []
                # Then add the binding to each item #
                for el in rule.lhs[1:]:
                    new_statement = instantiate(el, binding)
                    rest.append(new_statement)
                r = Rule(
                    # See "logical_classes.py" line 93 for constructor for Rule
                    # The actual statement of the rule we're adding
                    # [[LHS - statements that need to be true], [to make RHS true]]
                    [rest, instantiate(rule.rhs, binding)],
                    # The facts/rules it's supported by, in this case the original params #
                    [rule, fact]
                )
                # print(r)
                # Assert this new rule in kb
                kb.kb_assert(r)

                # Mark the original param fact and rule as supporting the new rule
                kb.rules[kb.rules.index(rule)].supports_rules.append(r)
                kb.facts[kb.facts.index(fact)].supports_rules.append(r)
            else:
                we_learned_something = instantiate(rule.rhs, binding)
                ff = Fact(
                    # See "logical_classes.py" line 18 for constructor for Fact
                    # the actual statement of the rule we're adding #
                    we_learned_something,
                    # the facts/rules it's supported by, in this case the original params #
                    [rule, fact]
                )
                print(ff.__class__)
                kb.kb_assert(ff)

                # Mark the original param fact and rule as supporting the new rule
                kb.rules[kb.rules.index(rule)].supports_facts.append(ff)
                print(kb.rules.index(rule))
                kb.facts[kb.facts.index(fact)].supports_facts.append(ff)
                print(kb.facts.index(fact))




