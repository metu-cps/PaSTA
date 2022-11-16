import argparse
import json
import logging as log
import os
import re
from types import SimpleNamespace
from utils import *
import logging as log
from z3 import *

class Path:
    def __init__(self, clocks=[]):
        self.locations = []
        self.transitions = []
        self.cycles = []
        self.forbiddenTransitions = []
        self.assertions = []
        self.clockValues = []
        self.currentClockValues = {}
        for c in clocks:
            self.currentClockValues[c] = []
        self.clockValues.append({"in": self.currentClockValues.copy(), "out": {}})
        self.cycleCounters = []
    def copyFrom(self, obj):
        self.locations = obj.locations.copy()
        self.transitions = obj.transitions.copy()
        self.cycles = obj.cycles.copy()
        self.forbiddenTransitions = obj.forbiddenTransitions.copy()
        self.assertions = obj.assertions.copy()
        self.clockValues = []
        self.currentClockValues = {}
        for c in obj.currentClockValues:
            self.currentClockValues[c] = obj.currentClockValues[c].copy()
        for cv in obj.clockValues:
            self.clockValues.append({"in": {}, "out": {}})
            for c in cv["in"]:
                self.clockValues[-1]["in"][c] = cv["in"][c].copy()
            for c in cv["out"]:
                self.clockValues[-1]["out"][c] = cv["out"][c].copy()
        self.cycleCounters = obj.cycleCounters.copy()
        return self
    def addLocation(self, ta, location):
        if location in self.locations:
            if len(self.cycles) == 0 or self.cycles[-1][1] < self.locations.index(location) + 1:
                self.cycles.append([self.locations.index(location) + 1, len(self.locations)])
        self.locations.append(location)
        arrivingLocationInv = next((a.constraints for a in ta.invariants if a.location == location), [])
        for inv in arrivingLocationInv:
            term = inv
            for c in self.currentClockValues:
                term = replaceFullWord(term, c, ("+".join(self.currentClockValues[c])) or "0")
            self.assertions.append(term)
    def addTransition(self, ta, transition):
        self.transitions.append(transition)
        lastLocationIndex = len(self.locations) - 1
        leavingLocation = self.locations[lastLocationIndex]
        for c in self.currentClockValues:
            self.currentClockValues[c].append(f'd{lastLocationIndex}_{leavingLocation}')
        leavingLocationInv = next((a.constraints for a in ta.invariants if a.location == leavingLocation), [])
        for inv in leavingLocationInv:
            term = inv
            for c in self.currentClockValues:
                term = replaceFullWord(term, c, ("+".join(self.currentClockValues[c])) or "0")
            self.assertions.append(term)

        for g in transition.guardConstraints:
            term = g
            for c in self.currentClockValues:
                term = replaceFullWord(term, c, ("+".join(self.currentClockValues[c])) or "0")
            self.assertions.append(term)
        
        self.clockValues[-1]["out"] = self.currentClockValues.copy()
        for r in transition.reset:
            self.currentClockValues[r] = []
        self.clockValues.append({"in": self.currentClockValues.copy(), "out": {}})
    def toStr(self):
        if len(self.locations) == 1:
            return self.locations[0]
        if len(self.locations) == len(self.transitions) + 1:
            return ' - '.join(self.locations[i] + " - " + self.transitions[i].action for i,a in enumerate(self.transitions)) + ' - ' + self.locations[-1]
    def clockValuesToStr(self):
        parts = []
        for i,loc in enumerate(self.locations):
            parts.append(f"{loc} in: {self.clockValues[i]['in']} - {loc} out: {self.clockValues[i]['out']}")
        return '; '.join(parts)
    def cyclesToStr(self):
        return ', '.join(list(map(lambda a: str(a[0]) + " - " + str(a[1]), self.cycles)))
    def getCycleExpandedPath(self, ta):
        if len(self.cycles) == 0 or self.cycles[-1][1] != len(self.locations) - 1:
            return None
        lastCycle = self.cycles[-1]
        resettingClocks = set([item for sublist in map(lambda a: a.reset, self.transitions[lastCycle[0]-1: lastCycle[1]]) for item in sublist])
        unresettingClocks = list(filter(lambda a: a not in resettingClocks, ta.clocks))
        if len(unresettingClocks) == 0:
            return None
        self.cycleCounters.append(f"cc_{len(self.cycles)}")
        cycleDelays = [f"d{i}_{self.locations[i]}" for i in range(lastCycle[0], lastCycle[1]+1)]
        additionalTerm = f"({self.cycleCounters[-1]})*({'+'.join(cycleDelays)})"
        newPath = Path().copyFrom(self)
        for uc in unresettingClocks:
            newPath.clockValues[lastCycle[0] - 1]["out"][uc].append(additionalTerm)
            for i in range(lastCycle[0], lastCycle[1]):
                newPath.clockValues[i]["in"][uc].append(additionalTerm)
                newPath.clockValues[i]["out"][uc].append(additionalTerm)
            newPath.clockValues[lastCycle[1]]["in"][uc].append(additionalTerm)
        newPath.rebuildAssertions(ta)
        for i in range(lastCycle[0], lastCycle[1]+1):
            newPath.addTransition(ta, newPath.transitions[i-1])
            newPath.addLocation(ta, newPath.locations[i])
        newPath.forbiddenTransitions = [self.transitions[-1]]
        return newPath
    def rebuildAssertions(self, ta):
        self.assertions = []
        for i in range((len(self.transitions))):
            curLoc = self.locations[i]
            self.currentClockValues = self.clockValues[i]["in"]
            locationInv = next((a.constraints for a in ta.invariants if a.location == curLoc), [])
            for inv in locationInv:
                term = inv
                for c in self.currentClockValues:
                    term = replaceFullWord(term, c, ("+".join(self.currentClockValues[c])) or "0")
                self.assertions.append(term)
            self.currentClockValues = self.clockValues[i]["out"]
            for inv in locationInv:
                term = inv
                for c in self.currentClockValues:
                    term = replaceFullWord(term, c, ("+".join(self.currentClockValues[c])) or "0")
                self.assertions.append(term)
            curTransition = self.transitions[i]
            for g in curTransition.guardConstraints:
                term = g
                for c in self.currentClockValues:
                    term = replaceFullWord(term, c, ("+".join(self.currentClockValues[c])) or "0")
                self.assertions.append(term)
        self.currentClockValues = self.clockValues[-1]["in"]
        lastLocationInv = next((a.constraints for a in ta.invariants if a.location == self.locations[-1]), [])
        for inv in lastLocationInv:
            term = inv
            for c in self.currentClockValues:
                term = replaceFullWord(term, c, ("+".join(self.currentClockValues[c])) or "0")
            self.assertions.append(term)
        return
    def isLastLocationUnsafe(self, spec):
        if self.locations[-1] in spec.locations:
            log.info(f"\tPath ends in the unsafe location {self.locations[-1]}")
            return True
        return False
    def getNextTransitions(self, ta):
        return list(filter(lambda a: a.source == self.locations[-1], ta.transitions))
    def isFeasible(self, ta, restrictions):
        joinedAssertions = "And(" + str.join(", ", self.assertions) + ")"

        log.info(f"Checking path: {self.toStr()}")
        log.info(f"\tClocks: {self.clockValuesToStr()}")
        log.info(f"\tCycles: {self.cyclesToStr()}")
        log.info(f"\tCycles: {self.cycleCounters}")
        log.info(f"\tAssertions: {joinedAssertions}")
        delayNames = [f"d{i}_{x}" for i,x in enumerate(self.locations)]
        s = Optimize()
        for d in delayNames:
            if d in globals():
                del globals()[d]
            globals()[d] = Real(d)
            s.add(eval(f"{d} >= 0"))

        for c in self.cycleCounters:
            if c in globals():
                del globals()[c]
            globals()[c] = Int(c)
            s.add(eval(f"{c} >= 0"))

        for p in ta.parameters:
            if p.name in globals():
                del globals()[p.name]
            globals()[p.name] = Int(p.name)
            s.add(eval(f"{p.name} >= {p.lowerBound}"))
            s.add(eval(f"{p.name} <= {p.upperBound}"))
        
        s.add(eval(joinedAssertions))
        for r in restrictions:
            s.add(r)

        c = s.check()
        if c.r == 1:
            log.debug(f"\tPath is feasible. A model is : {s.model()}")
            return True
        else:
            log.debug("Path is infeasible")
            return False
    def makeInfeasible(self, ta, restrictions):
        log.info("\tTrying to make the path infeasible")
        g = Goal()
        t = Tactic('qe')
        if len(self.cycleCounters) > 0:
            t = With(t, qe_nonlinear=True)

        delayNames = [f"d{i}_{x}" for i,x in enumerate(self.locations)]

        delayAssertions = []
        for d in delayNames:
            if d in globals():
                del globals()[d]
            globals()[d] = Real(d)
            # delayAssertions.append(f"{d} >= 0")

        cycleAssertions = []
        for c in self.cycleCounters:
            if c in globals():
                del globals()[c]
            globals()[c] = Real(c)
            # cycleAssertions.append(f"{c} >= 0")

        for p in ta.parameters:
            if p.name in globals():
                del globals()[p.name]
            globals()[p.name] = Int(p.name)
        assertionsWithDelays = list(filter(lambda a: bool(re.match(r".*d\d+_", a)), self.assertions))
        joinedAssertions = "And(" + str.join(", ", assertionsWithDelays + delayAssertions + cycleAssertions) + ")"
        
        qeArgs = str.join(", ", delayNames + self.cycleCounters)
        quantifiedDelayConstraint = f"Not(Exists([{qeArgs}], {joinedAssertions}))"
        g.add(eval(quantifiedDelayConstraint))

        qeResult = t.apply(g)
        delayEliminatedConstraint = qeResult.as_expr()
        if delayEliminatedConstraint == False:
            log.info("\tDelays could not be eliminated from the constraints of the unsafe path. Cannot make the path infeasible. PTA cannot be made safe.")
            return None

        log.info("\tDelays are eliminated from the constraints of the unsafe path. Will verify first, then check its feasibility.")
        if len(self.cycleCounters) == 0:
            delayEliminatedConstraint = self.toDnf(delayEliminatedConstraint, ta.parameters)

        newRestrictions = restrictions.copy()
        newRestrictions.append(delayEliminatedConstraint)

        if self.isFeasible(ta, newRestrictions) == True: # path is still feasible!
            log.info(f"\tShould not fall here! Found constraints cannot make the unsafe path infeasible!")
            return None

        if solveParametricConstraints(ta.parameters, [], newRestrictions) == False:
            log.info(f"\tThere is not a parameter valuation satisfying the new constraints.")
            return None
        
        log.info(f"\tCan make the unsafe path infeasible. New restrictions are: {delayEliminatedConstraint} and {newRestrictions}")
        return delayEliminatedConstraint
    def toCnf(self, constraint):
        t = Then(With('simplify', elim_and=True, elim_to_real=True), 'elim-term-ite', 'tseitin-cnf')
        g = Goal()
        g.add(constraint)
        return t.apply(g).as_expr()
    def simplifyCnf(self, cnf, taParameters):
        try:
            t = Then('simplify', 'propagate-values', ParThen('split-clause', 'propagate-ineqs'), 'simplify', 'ctx-simplify')
            g = Goal()
            g.add(cnf)
            for i in range(0, len(taParameters)):
                g.add(eval(f"{taParameters[i].name} >= {taParameters[i].lowerBound}"))
                g.add(eval(f"{taParameters[i].name} <= {taParameters[i].upperBound}"))
            simplifiedCnf = t.apply(g).as_expr()
            return simplifiedCnf
        except:
            return cnf
    def toDnf(self, constraint, taParameters):
        # return constraint
        cnf = self.toCnf(constraint)
        simplifiedCnf = self.simplifyCnf(cnf, taParameters)
        # return simplifiedCnf #todo
        t = Then(Tactic('simplify'), 'fm', Repeat(OrElse(Then('split-clause', 'simplify', 'solve-eqs', 'ctx-simplify', 'ctx-solver-simplify'), Tactic('skip'))))
        g = Goal()
        g.add(simplifiedCnf)
        dnf = t.apply(g).as_expr()
        self._checkUnsatDnfTerms(dnf)
        return dnf
    def _checkUnsatDnfTerms(self, dnf):
        unsat = 0
        for i in range(dnf.num_args()):
            g = Goal()
            g.add(dnf.arg(i))
            s = Solver()
            s.add(g)
            c = s.check()
            if c.r != 1:
                log.info(f"\tUnsatisfiable term in DNF: {dnf.arg(i)}")
                unsat = unsat + 1
        log.info(f"\tDNF has {unsat}/{dnf.num_args()} unsatisfiable terms\n")


def solveSafetyProblem(ta, spec, roundIndex):
    log.info(f'Solving problem "{spec.name}" on TA "{ta.name}" #{roundIndex}')
    initialPath = Path(ta.clocks)
    initialPath.addLocation(ta, ta.initialLocation)
    pathList = [initialPath]
    restrictions = []
    while len(pathList) > 0:
        path = pathList.pop()
        if path.isFeasible(ta, restrictions) == False:
            continue
        if path.isLastLocationUnsafe(spec):
            infeasibleMakingConstraint = path.makeInfeasible(ta, restrictions)
            if infeasibleMakingConstraint == None:
                restrictions = None
                break
            restrictions.append(infeasibleMakingConstraint)
        nextTransitions = path.getNextTransitions(ta)
        for nt in nextTransitions:
            if nt in path.forbiddenTransitions:
                continue
            count = len(list(filter(lambda a: a == nt.target, path.locations)))
            newPath = Path().copyFrom(path)
            newPath.addTransition(ta, nt)
            newPath.addLocation(ta, nt.target)
            pathList.append(newPath)
            if count == 1:
                log.info(f"\tWill be a cycle when {nt.target} is appended")
                log.info(f"\tWill append once and forbid the transition ({nt.source}, {nt.action}, {nt.target}) for that path in future explorations")
                newPath.forbiddenTransitions.append(nt)
                cycleExpandedPath = path.getCycleExpandedPath(ta)
                if cycleExpandedPath:
                    log.info(f"\tAdded cycle expanded path: {cycleExpandedPath.toStr()}")
                    pathList.append(cycleExpandedPath)
    if restrictions == None:
        log.info(f"PTA cannot be made safe")
        return
    else:
        log.info(f"PTA can be made safe with the following restrictions:\n{restrictions}")
        solveParametricConstraints(ta.parameters, spec.costCoefficients, restrictions)
    return

def solveParametricConstraints(taParameters, costCoefficients, restrictions):
        s = Optimize()

        for p in taParameters:
            if p.name in globals():
                del globals()[p.name]
            globals()[p.name] = Int(p.name)
            s.add(eval(f"{p.name} >= {p.lowerBound}"))
            s.add(eval(f"{p.name} <= {p.upperBound}"))
        s.add(restrictions)

        cost = Real('cost')
        costArgs = ["0"]
        for p in taParameters:
            cc = next(filter(lambda a: a.name == p.name, costCoefficients), None)
            if cc != None:
                costArgs.append(f"({cc.value}) * {p.name}")

        s.add(eval(f"{'+'.join(costArgs)} == cost"))

        h = s.minimize(cost)
        c = s.check()
        s.lower(h)
        m = s.model()

        if c.r == 1:
            parameterValuation = []
            for p in taParameters:
                parameterValuation.append(f"{p.name}: {m[eval(p.name)]}")
            log.info(f"\tOverall Result: Feasible with score ({m[cost]}) and values {', '.join(parameterValuation)}")
            return True
        else:
            log.info("\tOverall Result: Not feasible")
            return False


def solve(specPath, roundCount):
    for i in range(roundCount):
        with open(specPath) as input_file:
            spec = json.load(input_file, object_hook=lambda d: SimpleNamespace(**d))
        with open(os.path.join(os.path.dirname(specPath), spec.taPath)) as input_file:
            ta = json.load(input_file, object_hook=lambda d: SimpleNamespace(**d))
        if hasattr(spec, 'parameters'):
            for sp in spec.parameters:
                for ap in ta.parameters:
                    if sp.name != ap.name:
                        continue
                    if hasattr(sp, 'lowerBound'):
                        ap.lowerBound = sp.lowerBound
                    if hasattr(sp, 'upperBound'):
                        ap.upperBound = sp.upperBound
        if spec.type == "safety":
            solveSafetyProblem(ta, spec, i + 1)
    return

def replaceFullWord(str, search, replace):
    return re.sub(r"\b" + search + r"\b", replace, str)
    
if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '-i', '--input',
        help='Space separated list of spec json files as inputs',
        dest="inputPaths",
        nargs='+',
        required=False)
    parser.add_argument(
        '-d', '--debug',
        help="Print debugging statements",
        action="store_const", dest="loglevel", const=log.DEBUG,
        default=log.DEBUG,
    )
    parser.add_argument(
        '-v', '--verbose',
        help="Be verbose",
        action="store_const", dest="loglevel", const=log.INFO
    )
    parser.add_argument(
        '-r', '--round',
        help='Number of rounds to repeat for each input',
        dest="roundCount", type=int, default=1
    )
    args = parser.parse_args()

    log.basicConfig(
        level=args.loglevel,
        filename="log.txt",
        format='%(asctime)s.%(msecs)03d %(levelname)-8s %(message)s',
        datefmt='%H:%M:%S',
        filemode='w'
    )
    for p in args.inputPaths:
        solve(p, args.roundCount)