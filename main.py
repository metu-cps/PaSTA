import argparse
import glob
import json
import logging as log
import os
import re
import subprocess
import timeit
from types import SimpleNamespace
from z3 import *


class Stats:
  def __init__(self):
    self.linearFeasibilityCheckCount = 0
    self.linearFeasibilityCheckTime = 0
    self.nonlinearFeasibilityCheckCount = 0
    self.nonlinearFeasibilityCheckTime = 0
    self.linearFeasiblePathCount = 0
    self.linearFeasibleUnsafePathCount = 0
    self.nonlinearFeasiblePathCount = 0
    self.nonlinearFeasibleUnsafePathCount = 0
    self.linearQeTime = 0
    self.nonlinearQeTime = 0
    self.total_time = 0
    self.name = ''
  @staticmethod
  def __to_ms(sec):
      return '{0:.{1}f}'.format(sec * 1000, 2)
  def to_str(self):
    linearFeasibilityCheckTime = Stats.__to_ms(self.linearFeasibilityCheckTime)
    nonlinearFeasibilityCheckTime = Stats.__to_ms(self.nonlinearFeasibilityCheckTime)
    linearQeTime = Stats.__to_ms(self.linearQeTime)
    nonlinearQeTime = Stats.__to_ms(self.nonlinearQeTime)
    total_time = Stats.__to_ms(self.total_time)
    z3_time = Stats.__to_ms(self.linearFeasibilityCheckTime + self.nonlinearFeasibilityCheckTime + self.linearQeTime + self.nonlinearQeTime)
    str = "automata\tpath counts\tfeasibility check time\tqe time\tZ3 time / total time\n"
    str += f"{self.name}\t{self.linearFeasibilityCheckCount} / {self.linearFeasiblePathCount} / {self.linearFeasibleUnsafePathCount} - "
    str += f"{self.nonlinearFeasibilityCheckCount} / {self.nonlinearFeasiblePathCount} / {self.nonlinearFeasibleUnsafePathCount}\t"
    str += f"{linearFeasibilityCheckTime} / {nonlinearFeasibilityCheckTime}\t"
    str += f"{linearQeTime} / {nonlinearQeTime}\t"
    str += f"{z3_time} / {total_time}"
    return str

class Path:
    _decisionVariables = []
    def __init__(self):
        self.locations = []
        self.transitions = []
        self.clockValues = []
        self.assertions = []
        self.cycleLocations = []
        self.cycles = []
        self.cycleCounters = []
    @staticmethod
    def getInitialPath(ta):
        p = Path()
        p.clockValues.append({"in": {c: [] for c in ta.clocks}, "out": {}})
        p.__addLocation(ta, ta.initialLocation)
        return p
    @staticmethod
    def copyFrom(obj):
        p = Path()
        p.locations = obj.locations.copy() # internals not modified, no need to deep copy
        p.transitions = obj.transitions.copy() # internals not modified, no need to deep copy
        p.clockValues = Path.copyClockValues(obj.clockValues) # internals modified, need to deep copy
        p.assertions = obj.assertions.copy() # simple string list
        p.cycleLocations = obj.cycleLocations.copy() # simple string list
        p.cycles = obj.cycles.copy() # simple list of list of two integers
        p.cycleCounters = obj.cycleCounters.copy() # simple string list
        return p
    @staticmethod
    def copyClockValues(clockValues):
        newClockValues = []
        for cv in clockValues:
            newClockValues.append({"in": Path.copyPointClockValues(cv["in"]), "out": Path.copyPointClockValues(cv["out"])})
            if "lb-in" in cv:
                newClockValues[-1]["lb-in"] = Path.copyPointClockValues(cv["lb-in"])
                newClockValues[-1]["lb-out"] = Path.copyPointClockValues(cv["lb-out"])
                newClockValues[-1]["ub-in"] = Path.copyPointClockValues(cv["ub-in"])
                newClockValues[-1]["ub-out"] = Path.copyPointClockValues(cv["ub-out"])
                newClockValues[-1]["reset-in-f"] = Path.copyPointClockValues(cv["reset-in-f"])
                newClockValues[-1]["reset-in-a"] = Path.copyPointClockValues(cv["reset-in-a"])
                newClockValues[-1]["reset-in-l"] = Path.copyPointClockValues(cv["reset-in-l"])
                newClockValues[-1]["reset-out-f"] = Path.copyPointClockValues(cv["reset-out-f"])
                newClockValues[-1]["reset-out-a"] = Path.copyPointClockValues(cv["reset-out-a"])
                newClockValues[-1]["reset-out-l"] = Path.copyPointClockValues(cv["reset-out-l"])
        return newClockValues
    @staticmethod
    def copyPointClockValues(clockValues):
        newClockValues = {}
        for c in clockValues:
            newClockValues[c] = clockValues[c].copy()
        return newClockValues

    def __addAssertionsFromConstraint(self, constraints, currentClockValues):
        for t in constraints:
            term = t
            for c in currentClockValues:
                term = replaceFullWord(term, c, ("+".join(currentClockValues[c])) or "0")
            self.assertions.append(term)

    def __addLocation(self, ta, location):
        # consider the path l1, l2, l1, l2. only element in cycles should be [0, 1].
        # below check prevents [1, 2] from going into the cycles.
        if location in self.locations and location not in self.cycleLocations:
            self.cycles.append([self.locations.index(location), len(self.locations) - 1])
            self.cycleLocations += self.locations[self.locations.index(location):]

        self.locations.append(location)
        arrivingLocationInv = next((a.constraints for a in ta.invariants if a.location == location), [])
        self.__addAssertionsFromConstraint(arrivingLocationInv, self.clockValues[-1]["in"])

    def addTransitionLocation(self, ta, transition):
        self.transitions.append(transition)
        leavingLocation = self.locations[-1]
        leavingLocationIndex = len(self.locations) - 1
        self.clockValues[-1]["out"] = Path.copyPointClockValues(self.clockValues[-1]["in"])
        for c in self.clockValues[-1]["out"]:
            self.clockValues[-1]["out"][c].append(f'd{leavingLocationIndex}_{leavingLocation}')

        leavingLocationInv = next((a.constraints for a in ta.invariants if a.location == leavingLocation), [])
        self.__addAssertionsFromConstraint(leavingLocationInv, self.clockValues[-1]["out"])
        self.__addAssertionsFromConstraint(transition.guardConstraints, self.clockValues[-1]["out"])

        self.clockValues.append({"in": Path.copyPointClockValues(self.clockValues[-1]["out"]), "out": {}})
        for r in transition.reset:
            self.clockValues[-1]["in"][r] = []
        self.__addLocation(ta, transition.target)
        return
    def logDetails(self):
        info = []
        log.info("\tPath:")
        if len(self.locations) == 1:
            log.info("\t\t" + self.locations[0])
        elif len(self.locations) == len(self.transitions) + 1:
            log.info("\t\t" + ' - '.join(self.locations[i] + " - " + self.transitions[i].action for i,a in enumerate(self.transitions)) + ' - ' + self.locations[-1])
        log.debug("\tClock Values:")
        for i,loc in enumerate(self.locations):
            infoLine = f"\t\t{loc}\n\t\t\tin: {self.clockValues[i]['in']}\n\t\t\tout: {self.clockValues[i]['out']}"
            if "lb-in" in self.clockValues[i]:
                infoLine += f"\n\t\t\tlb-in: {self.clockValues[i]['lb-in']}\n\t\t\tlb-out: {self.clockValues[i]['lb-out']}"
                infoLine += f"\n\t\t\tub-in: {self.clockValues[i]['ub-in']}\n\t\t\tub-out: {self.clockValues[i]['ub-out']}"
                infoLine += f"\n\t\t\treset-in-f: {self.clockValues[i]['reset-in-f']}\n\t\t\treset-out-f: {self.clockValues[i]['reset-out-f']}"
                infoLine += f"\n\t\t\treset-in-a: {self.clockValues[i]['reset-in-a']}\n\t\t\treset-out-a: {self.clockValues[i]['reset-out-a']}"
                infoLine += f"\n\t\t\treset-in-l: {self.clockValues[i]['reset-in-l']}\n\t\t\treset-out-l: {self.clockValues[i]['reset-out-l']}"
            log.debug(infoLine)
        log.debug("\tAssertions:")
        log.debug(f'\t\t{"And(" + str.join(", ", self.assertions) + ")"}')
        if len(self.cycleCounters) > 0:
            log.info("\tCycle Indices:")
            log.info("\t\t" + ', '.join(list(map(lambda a: str(a[0]) + " - " + str(a[1]), self.cycles))))
            log.debug("\tCycle Counters:")
            log.debug("\t\t" + str(self.cycleCounters))
    def isFeasible(self, ta, restrictions, reportMinCycles, realValuedParameters):
        log.info(f"Checking feasibility of the path")
        self.logDetails()
        ctx = self.__initDecisionVariables(ta, Int, realValuedParameters)

        delayNames = [f"d{i}_{x}" for i,x in enumerate(self.locations)]
        optimize = Optimize(ctx=ctx)
        for c in self.cycles:
            for i in range(c[0], c[1] + 1):
                optimize.add(eval(f"f{i}_{self.locations[i]} >= 0"))
                optimize.add(eval(f"a{i}_{self.locations[i]} >= 0"))
        for d in delayNames:
            optimize.add(eval(f"{d} >= 0"))

        for c in self.cycleCounters:
            optimize.add(eval(f"{c} >= 0"))
        if reportMinCycles and len(self.cycleCounters) > 0:
            if "cost" in globals():
                del globals()["cost"]
            globals()["cost"] = Real('cost', ctx=ctx)

        for p in ta.parameters:
            optimize.add(eval(f"{p.name} >= {p.lowerBound}"))
            optimize.add(eval(f"{p.name} <= {p.upperBound}"))
        
        if len(self.assertions) > 0:
            joinedAssertions = "And(" + str.join(", ", self.assertions) + ")"
            e = eval(joinedAssertions)
            if str(e) != 'And(True)':
              optimize.add(eval(joinedAssertions))
        for r in restrictions:
            if type(r) == bool:
                optimize.add(r)
            else:
                optimize.add(r.translate(ctx))

        if reportMinCycles and len(self.cycleCounters) > 0:
            optimize.add(eval(f"cost == {'+'.join(self.cycleCounters)}"))
            h = optimize.minimize(eval("cost"))
            c = optimize.check()
            if c.r == 1:
                optimize.lower(h)
        else:
            c = optimize.check()

        if c.r == 1:
            m = optimize.model()
            log.info(f"\tPath is feasible. A model is : {m}")
            return True
        else:
            log.info("Path is infeasible")
            return False
    def endsInUnsafeLocation(self, spec):
        if self.locations[-1] in spec.locations:
            log.info(f"\tPath ends in the unsafe location {self.locations[-1]}")
            return True
        return False
    def getNextTransitions(self, ta):
        return list(filter(lambda a: a.source == self.locations[-1], ta.transitions))
    def makeInfeasible(self, ta, restrictions, realValuedParameters):
        makeInfeasibleStart = timeit.default_timer()
        log.info("\tTrying to make the path infeasible")
        cycleCounterType = eval(ta.cycleCounterType) if hasattr(ta, "cycleCounterType") else Real # TODO: ideally, this should not be here
        ctx = self.__initDecisionVariables(ta, cycleCounterType, realValuedParameters)
        goal = Goal(ctx=ctx)

        firstDelayNames = []
        averageDelayNames = []
        for c in self.cycles:
            for i in range(c[0], c[1] + 1):
                firstDelayNames.append(f"f{i}_{self.locations[i]}")
                averageDelayNames.append(f"a{i}_{self.locations[i]}")
        delayNames = [f"d{i}_{x}" for i,x in enumerate(self.locations)]
        t = Tactic('qe', ctx=ctx)
        if len(self.cycleCounters) == 0:
          nonNegativeDelays = list(map(lambda a: f"{a} >= 0", delayNames))
          joinedAssertions = "And(" + str.join(", ", nonNegativeDelays + self.assertions) + ")"
        else:
          nonnegativeCycles = [] if cycleCounterType == Real else list(map(lambda a: f"{a} >= 0", self.cycleCounters)) # TODO: ideally, this should not be here, either
          joinedAssertions = "And(" + str.join(", ", self.assertions + nonnegativeCycles) + ")"
          t = With(t, qe_nonlinear=True, ctx=ctx)
            
        qeArgs = str.join(", ", firstDelayNames + averageDelayNames + delayNames + self.cycleCounters)
        quantifiedDelayConstraint = f"Not(Exists([{qeArgs}], {joinedAssertions}))"
        goal.add(eval(quantifiedDelayConstraint))
        log.debug(f"\tQuantified Constraint: {quantifiedDelayConstraint}")

        qeResult = t.apply(goal)
        delayEliminatedConstraint = qeResult.as_expr()
        makeInfeasibleTime = timeit.default_timer() - makeInfeasibleStart
        if delayEliminatedConstraint == False:
            log.info("\tDelays could not be eliminated from the constraints of the unsafe path. Cannot make the path infeasible. PTA cannot be made safe.")
            return False

        log.info("\tDelays are eliminated from the constraints of the unsafe path.")
        if len(self.cycleCounters) == 0:
            ta_stats.linearQeTime += makeInfeasibleTime
            delayEliminatedConstraint = self.__toDnf(delayEliminatedConstraint, ta.parameters, ctx)
        else:
            ta_stats.nonlinearQeTime += makeInfeasibleTime
        log.debug(f"\tNew Restrictions: {delayEliminatedConstraint}")

        restrictions.append(delayEliminatedConstraint)
        if log.root.level == log.STATS:
            return delayEliminatedConstraint
        log.info("\tVerifying unsafe path's infeasibility with the new restriction.")
        isFeasible = self.isFeasible(ta, restrictions, False, realValuedParameters)
        if isFeasible == True: # path is still feasible!
            log.info(f"\tShould not fall here! Found constraints cannot make the unsafe path infeasible!")
            return False

        log.info("\tChecking updated restrictions list does not yield an empty parameter valuation.")
        hasParameterValuation = solveParametricConstraints(ta.parameters, restrictions, [], realValuedParameters)
        if hasParameterValuation == False:
            log.info(f"\tThere is not a parameter valuation satisfying the new constraints.")
            return False
        log.info(f"\tCan make the unsafe path infeasible. New restrictions are: {restrictions}")
        return True
    def __toCnf(self, constraint, ctx):
        t = Then(With(Tactic('simplify', ctx=ctx), elim_and=True, elim_to_real=True, ctx=ctx), 'elim-term-ite', 'tseitin-cnf', ctx=ctx)
        g = Goal(ctx=ctx)
        g.add(constraint)
        return t.apply(g).as_expr()
    def __simplifyCnf(self, cnf, taParameters, ctx):
        try:
            t = Then('simplify', 'propagate-values', ParThen('split-clause', 'propagate-ineqs', ctx=ctx), 'simplify', 'ctx-simplify', ctx=ctx)
            g = Goal(ctx=ctx)
            g.add(cnf)
            for i in range(0, len(taParameters)):
                g.add(eval(f"{taParameters[i].name} >= {taParameters[i].lowerBound}"))
                g.add(eval(f"{taParameters[i].name} <= {taParameters[i].upperBound}"))
            simplifiedCnf = t.apply(g).as_expr()
            return simplifiedCnf
        except Exception as error:
            log.exception(error)
            log.debug(f"__simplifyCnf could not simplify. returning: {cnf}")
            return cnf
    def __toDnf(self, constraint, taParameters, ctx):
        # return constraint
        cnf = self.__toCnf(constraint, ctx)
        if cnf.decl().name() != 'and':
            return cnf
        simplifiedCnf = self.__simplifyCnf(cnf, taParameters, ctx)
        # return simplifiedCnf #todo
        t = Then(Tactic('simplify', ctx=ctx), 'fm', Repeat(OrElse(Then('split-clause', 'simplify', 'solve-eqs', 'ctx-simplify', 'ctx-solver-simplify', ctx=ctx), Tactic('skip', ctx=ctx), ctx=ctx), ctx=ctx), ctx=ctx)
        g = Goal(ctx=ctx)
        g.add(simplifiedCnf)
        dnf = t.apply(g).as_expr()
        self._checkUnsatDnfTerms(dnf, ctx)
        return dnf
    def _checkUnsatDnfTerms(self, dnf, ctx):
        unsat = 0
        if dnf.decl().name != 'or':
          return
        for i in range(dnf.num_args()):
            g = Goal(ctx=ctx)
            g.add(dnf.arg(i))
            s = Solver(ctx=ctx)
            s.add(g)
            c = s.check()
            if c.r != 1:
                log.info(f"\tUnsatisfiable term in DNF: {dnf.arg(i)}")
                unsat = unsat + 1
        log.info(f"\tDNF has {unsat}/{dnf.num_args()} unsatisfiable terms\n")
    def __initDecisionVariables(self, ta, cycleCounterType, realValuedParameters):
        ctx = Context()
        for d in Path._decisionVariables:
            if d in globals():
                del globals()[d]
        Path._decisionVariables = []
        delayNames = [f"d{i}_{x}" for i,x in enumerate(self.locations)]
        for d in delayNames:
            Path._decisionVariables.append(d)
            globals()[d] = Real(d,ctx=ctx)
        firstDelayNames = [f"f{i}_{self.locations[i]}" for cycle in self.cycles for i in range(cycle[0], cycle[1]+1)]
        averageDelayNames = [f"a{i}_{self.locations[i]}" for cycle in self.cycles for i in range(cycle[0], cycle[1]+1)]
        for d in firstDelayNames:
            Path._decisionVariables.append(d)
            globals()[d] = Real(d,ctx=ctx)
        for d in averageDelayNames:
            Path._decisionVariables.append(d)
            globals()[d] = Real(d,ctx=ctx)
        if cycleCounterType == Int:
            for c in self.cycleCounters:
                Path._decisionVariables.append(c)
                globals()[c] = Int(c,ctx=ctx)
        else:
            for c in self.cycleCounters:
                Path._decisionVariables.append(c)
                globals()[c] = Real(c,ctx=ctx)
        if realValuedParameters:
            for p in ta.parameters:
                Path._decisionVariables.append(p.name)
                globals()[p.name] = Real(p.name,ctx=ctx)
        else:
            for p in ta.parameters:
                Path._decisionVariables.append(p.name)
                globals()[p.name] = Int(p.name,ctx=ctx)
        return ctx
    def __getConstraintType(self, constraint, index, resetIndices):
        if ">" in constraint:
            args = constraint.split(">")
        elif "<" in constraint:
            args = constraint.split("<")
            args.reverse()
        else:
            raise ValueError("Unsupported automaton. Equals check in constraints.") 
        for x in resetIndices:
            if resetIndices[x] == None:
                if x in args[0]:
                    return 1, x
                elif x in args[1]:
                    return 3, x
            else:
                if x in constraint and index > resetIndices[x]:
                    return 2, x
                elif x in constraint and index <= resetIndices[x]:
                    self.logDetails()
                    raise ValueError("Unsupported automaton. In a cycle, clock is used first then reset.") 
        return 4, None
    def getCycleExpandedPath(self, ta):
        if len(self.cycles) == 0 or len(self.cycles) == len(self.cycleCounters) or self.cycles[-1][1] != len(self.locations) - 2:
            return None
        lastCycle = self.cycles[-1]
        lastCycleResetIndices = {c: None for c in ta.clocks}
        for i in range(lastCycle[0], lastCycle[1] + 1):
            for x in self.transitions[i].reset:
                if lastCycleResetIndices[x]:
                    continue
                lastCycleResetIndices[x] = i
        for x in self.transitions[lastCycle[1]].reset:
            lastCycleResetIndices[x] = -1

        nonresettingClocks = list(filter(lambda a: lastCycleResetIndices[a] == None, ta.clocks))
        if len(nonresettingClocks) == 0: # no need to run more cycles
            log.info("All clocks get reset in the cycle, so nothing will happen by cycling more. Will not add the cyclic path")
            return None
        path = Path.copyFrom(self)
        path.cycleCounters.append(f"cc_{len(path.cycles)}")
        # clear assertions from last cycle first
        lastCycleDelays = [f"d{a}_{path.locations[a]}" for a in range(lastCycle[0], len(path.locations))]
        path.assertions = list(filter(lambda a: any(b in a for b in lastCycleDelays) == False, path.assertions))
        # introduce new delay decision variables
        firstCycleDelays = [f"f{a}_{path.locations[a]}" for a in range(lastCycle[0], len(path.locations)-1)]
        averageDelays = [f"a{a}_{path.locations[a]}" for a in range(lastCycle[0], len(path.locations)-1)]
        sumFirstCycleDelays = "+".join(firstCycleDelays)
        sumAverageDelaysTimesCc = f"{path.cycleCounters[-1]}*({'+'.join(averageDelays)})"
        # rebuild clock values
        for i in range(lastCycle[0], lastCycle[1] + 1):
            path.clockValues[i]["lb-in"] = {}
            path.clockValues[i]["lb-out"] = {}
            path.clockValues[i]["ub-in"] = {}
            path.clockValues[i]["ub-out"] = {}
            path.clockValues[i]["reset-in-f"] = {}
            path.clockValues[i]["reset-in-a"] = {}
            path.clockValues[i]["reset-in-l"] = {}
            path.clockValues[i]["reset-out-f"] = {}
            path.clockValues[i]["reset-out-a"] = {}
            path.clockValues[i]["reset-out-l"] = {}
            for x in ta.clocks:
                if x in nonresettingClocks:
                    xValArrive = path.clockValues[lastCycle[0]]["in"][x] + [f"f{a}_{path.locations[a]}" for a in range(lastCycle[0], i)]
                    xValLeave = path.clockValues[lastCycle[0]]["in"][x] + [f"f{a}_{path.locations[a]}" for a in range(lastCycle[0], i + 1)]
                    path.clockValues[i]["lb-in"][x] = xValArrive
                    path.clockValues[i]["lb-out"][x] = xValLeave

                    xValArrive = path.clockValues[lastCycle[0]]["in"][x] + [f"d{a}_{path.locations[a]}" for a in range(lastCycle[0], i)]
                    xValLeave = path.clockValues[lastCycle[0]]["in"][x] + [f"d{a}_{path.locations[a]}" for a in range(lastCycle[0], i + 1)]
                    xValArrive += [sumFirstCycleDelays, sumAverageDelaysTimesCc]
                    xValLeave += [sumFirstCycleDelays, sumAverageDelaysTimesCc]
                    path.clockValues[i]["ub-in"][x] = xValArrive
                    path.clockValues[i]["ub-out"][x] = xValLeave
                else:
                    xValArriveF = [re.sub(r'^d', 'f', a) for a in path.clockValues[i]["in"][x]]
                    xValArriveA = [re.sub(r'^d', 'a', a) for a in path.clockValues[i]["in"][x]]
                    xValArriveA = list(filter(lambda a: a in averageDelays, xValArriveA))
                    xValArriveL = [re.sub(r'^a', 'd', a) for a in xValArriveA]
                    xValLeaveF = [re.sub(r'^d', 'f', a) for a in path.clockValues[i]["out"][x]]
                    xValLeaveA = [re.sub(r'^d', 'a', a) for a in path.clockValues[i]["out"][x]]
                    xValLeaveA = list(filter(lambda a: a in averageDelays, xValLeaveA))
                    xValLeaveL = [re.sub(r'^a', 'd', a) for a in xValLeaveA]
                    path.clockValues[i]["reset-in-f"][x] = xValArriveF
                    path.clockValues[i]["reset-in-a"][x] = xValArriveA
                    path.clockValues[i]["reset-in-l"][x] = xValArriveL
                    path.clockValues[i]["reset-out-f"][x] = xValLeaveF
                    path.clockValues[i]["reset-out-a"][x] = xValLeaveA
                    path.clockValues[i]["reset-out-l"][x] = xValLeaveL
        
        for x in ta.clocks:
            if x in nonresettingClocks:
                path.clockValues[-1]["in"][x] = path.clockValues[-2]["ub-out"][x].copy()
            elif x in path.transitions[lastCycle[1]].reset:
                path.clockValues[-1]["in"][x] = []
            else:
                path.clockValues[-1]["in"][x] = path.clockValues[-2]["reset-out-l"][x].copy()

        for i in range(lastCycle[0], lastCycle[1] + 1):
            cycleLocationInv = next((a.constraints for a in ta.invariants if a.location == path.locations[i]), [])
            for inv in cycleLocationInv:
                t, x = path.__getConstraintType(inv, i, lastCycleResetIndices)
                if t == 1:
                    path.assertions.append(replaceFullWord(inv, x, ("+".join(path.clockValues[i]["lb-in"][x])) or "0"))
                    path.assertions.append(replaceFullWord(inv, x, ("+".join(path.clockValues[i]["lb-out"][x])) or "0"))
                elif t == 2:
                    path.assertions.append(replaceFullWord(inv, x, ("+".join(path.clockValues[i]["reset-in-f"][x])) or "0"))
                    path.assertions.append(replaceFullWord(inv, x, ("+".join(path.clockValues[i]["reset-in-a"][x])) or "0"))
                    path.assertions.append(replaceFullWord(inv, x, ("+".join(path.clockValues[i]["reset-in-l"][x])) or "0"))
                    path.assertions.append(replaceFullWord(inv, x, ("+".join(path.clockValues[i]["reset-out-f"][x])) or "0"))
                    path.assertions.append(replaceFullWord(inv, x, ("+".join(path.clockValues[i]["reset-out-a"][x])) or "0"))
                    path.assertions.append(replaceFullWord(inv, x, ("+".join(path.clockValues[i]["reset-out-l"][x])) or "0"))
                elif t == 3:
                    path.assertions.append(replaceFullWord(inv, x, ("+".join(path.clockValues[i]["ub-in"][x])) or "0"))
                    path.assertions.append(replaceFullWord(inv, x, ("+".join(path.clockValues[i]["ub-out"][x])) or "0"))
            transitionGuard = path.transitions[i].guardConstraints
            for g in transitionGuard:
                t, x = path.__getConstraintType(g, i, lastCycleResetIndices)
                if t == 1:
                    path.assertions.append(replaceFullWord(g, x, ("+".join(path.clockValues[i]["lb-out"][x])) or "0"))
                elif t == 2:
                    path.assertions.append(replaceFullWord(g, x, ("+".join(path.clockValues[i]["reset-out-f"][x])) or "0"))
                    path.assertions.append(replaceFullWord(g, x, ("+".join(path.clockValues[i]["reset-out-a"][x])) or "0"))
                    path.assertions.append(replaceFullWord(g, x, ("+".join(path.clockValues[i]["reset-out-l"][x])) or "0"))
                elif t == 3:
                    path.assertions.append(replaceFullWord(g, x, ("+".join(path.clockValues[i]["ub-out"][x])) or "0"))

        arrivingLocationInv = next((a.constraints for a in ta.invariants if a.location == path.locations[-1]), [])
        path.__addAssertionsFromConstraint(arrivingLocationInv, path.clockValues[-1]["in"])
        return path

###################################################################################

def solveSafetyProblem(ta, spec, reportMinCycles, realValuedParameters):
    log.info(f'Solving problem "{spec.name}" on TA "{ta.name}"')
    initialPath = Path.getInitialPath(ta)
    pathList = [initialPath]
    restrictions = []
    while len(pathList) > 0:
        path = pathList.pop()
        feasibilityCheckStart = timeit.default_timer()
        isFeasible = path.isFeasible(ta, restrictions, reportMinCycles, realValuedParameters)
        feasibilityCheckTime = timeit.default_timer() - feasibilityCheckStart
        if len(path.cycleCounters) == 0:
            ta_stats.linearFeasibilityCheckCount += 1
            ta_stats.linearFeasibilityCheckTime += feasibilityCheckTime
        else:
            ta_stats.nonlinearFeasibilityCheckCount += 1
            ta_stats.nonlinearFeasibilityCheckTime += feasibilityCheckTime
        if isFeasible == False:
            continue
        if len(path.cycleCounters) == 0:
            ta_stats.linearFeasiblePathCount += 1
        else:
            ta_stats.nonlinearFeasiblePathCount += 1
        if path.endsInUnsafeLocation(spec):
            if len(path.cycleCounters) == 0:
                ta_stats.linearFeasibleUnsafePathCount += 1
            else:
                ta_stats.nonlinearFeasibleUnsafePathCount += 1
            infeasibleMakingConstraint = path.makeInfeasible(ta, restrictions, realValuedParameters)
            if infeasibleMakingConstraint == False:
                log.info(f"PTA cannot be made safe")
                return
            continue
        lastLocationCount = len(list(filter(lambda a: a == path.locations[-1], path.locations)))
        if lastLocationCount == 2:
            log.info(f"\tFeasible path ends with a cycle")
            cycleExpandedPath = path.getCycleExpandedPath(ta)
            if cycleExpandedPath:
                log.info(f"\tAdded cycle expanded path")
                cycleExpandedPath.logDetails()
                pathList.append(cycleExpandedPath)
        nextTransitions = path.getNextTransitions(ta)
        for nt in nextTransitions:
            newPath = Path.copyFrom(path)
            newPath.addTransitionLocation(ta, nt)
            lastLocationCount = len(list(filter(lambda a: a == nt.target, newPath.locations)))
            if lastLocationCount == 3:
                log.info(f"\tLast location appears three times. Will skip the path:")
                newPath.logDetails()
                continue
            log.info(f"Adding path")
            newPath.logDetails()
            pathList.append(newPath)
    log.info("PTA can be made safe")
    log.debug(f"PTA can be made safe with the following restrictions:\n{restrictions}")
    solveParametricConstraints(ta.parameters, restrictions, spec.costCoefficients, realValuedParameters)
    return

def solveParametricConstraints(taParameters, restrictions, costCoefficients, realValuedParameters):
        log.info("Checking for the optimum solution")
        ctx = Context()
        s = Optimize(ctx=ctx)
        paramType = Real if realValuedParameters else Int
        for p in taParameters:
            if p.name in globals():
                del globals()[p.name]
            globals()[p.name] = paramType(p.name,ctx=ctx)
            s.add(eval(f"{p.name} >= {p.lowerBound}"))
            s.add(eval(f"{p.name} <= {p.upperBound}"))
        for r in restrictions:
            if type(r) == bool:
                s.add(r)
            else:
                s.add(r.translate(ctx))

        cost = Real('cost', ctx)
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

        if c.r != 1:
            log.stats("\tOverall Result: Not feasible")
            return False

        parameterValuation = []
        for p in taParameters:
            parameterValuation.append(f"{p.name}: {m[eval(p.name)]}")
        log.stats(f"\tOverall Result: Feasible with score ({m[cost]}) and values {', '.join(parameterValuation)}")
        return True

def replaceFullWord(str, search, replace):
    return re.sub(r"\b" + search + r"\b", replace, str)

def solve(specPath, reportMinCycles, realValuedParameters):
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
        ta_stats.name = ta.name
        solveSafetyProblem(ta, spec, reportMinCycles, realValuedParameters)
    return

def addLoggingLevel(levelName, levelNum, methodName=None):
  def logForLevel(self, message, *args, **kwargs):
      if self.isEnabledFor(levelNum):
          self._log(levelNum, message, args, **kwargs)
  def logToRoot(message, *args, **kwargs):
      log.log(levelNum, message, *args, **kwargs)

  if not methodName:
      methodName = levelName.lower()
  log.addLevelName(levelNum, levelName)
  setattr(log, levelName, levelNum)
  setattr(log.getLoggerClass(), methodName, logForLevel)
  setattr(log, methodName, logToRoot)

ta_stats = Stats()

def runBenchmarks():
    specs = glob.glob("Examples/**/*.safety*.json", recursive=True)
    for s in specs:
        o = os.path.basename(s)
        subprocess.run(["python", "main.py", "-i", s, "-o", f"{o}.Int.debug.log", "--reportMinCycles", "-d"])
        subprocess.run(["python", "main.py", "-i", s, "-o", f"{o}.Real.debug.log", "--reportMinCycles", "--realValuedParameters", "-d"])
        subprocess.run(["python", "main.py", "-i", s, "-o", f"{o}.Int.stats.log"])
        subprocess.run(["python", "main.py", "-i", s, "-o", f"{o}.Real.stats.log", "--realValuedParameters"])

if __name__ == '__main__':
    if len(sys.argv) == 1:
        runBenchmarks()
        exit()

    addLoggingLevel('STATS', log.FATAL + 5)
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '-i', '--input',
        help='Spec json files as input',
        dest="inputPath",
        required=False)
    parser.add_argument(
        '-o', '--output',
        help='Spec log files as output',
        dest="outputPath",
        required=False)
    parser.add_argument('--reportMinCycles', action=argparse.BooleanOptionalAction)
    parser.add_argument('--realValuedParameters', action=argparse.BooleanOptionalAction)
    parser.add_argument(
        '-d', '--debug',
        help="Print debugging statements",
        action="store_const", dest="loglevel", const=log.DEBUG,
        default=log.STATS,
    )
    parser.add_argument(
        '-v', '--verbose',
        help="Be verbose",
        action="store_const", dest="loglevel", const=log.INFO
    )
    args = parser.parse_args()

    if os.path.isdir("logs") == False:
        os.makedirs("logs")
    
    if args.loglevel == log.STATS:
      log.basicConfig(
          level=args.loglevel,
          filename=os.path.join("logs", args.outputPath or (os.path.basename(args.inputPath) + ".txt")),
          format='%(message)s',
          datefmt='%H:%M:%S',
          filemode='w'
      )
    else:
      log.basicConfig(
          level=args.loglevel,
          filename=os.path.join("logs", args.outputPath or (os.path.basename(args.inputPath) + ".txt")),
          format='%(asctime)s.%(msecs)03d %(levelname)-8s %(message)s',
          datefmt='%H:%M:%S',
          filemode='w'
      )
    start = timeit.default_timer()
    solve(args.inputPath, args.reportMinCycles, args.realValuedParameters)
    end = timeit.default_timer()
    ta_stats.total_time = end-start

    log.stats(ta_stats.to_str())
