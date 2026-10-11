import Lax109476Proofs.RamCertificateFamilies
import Lax109476Proofs.RamCertificateDecision
import Lax109476Proofs.RamRecoverCertificate
import Lax109476Proofs.RamCertificateSetup
import Lax109476Proofs.RamSolverFrontEnd

namespace Lax109476Proofs.RamExactSolverProgram

open Lax808846Proofs.Imp
open RamCertificateArrayRelabel

def optimalSystem : Com := isolated "optimal.recovery." RamCertificateFamilies.optimal
def infeasibleSystem : Com := isolated "infeasible.recovery." RamCertificateFamilies.infeasible
def unboundedSystem : Com := isolated "unbounded.recovery." RamCertificateFamilies.unbounded

def optimalDecision : Com := RamCertificateDecision.decideFeasible "optimal.recovery." "optimal.decision."
def infeasibleDecision : Com := RamCertificateDecision.decideFeasible "infeasible.recovery." "infeasible.decision."

def optimalRecovery : Com := isolated "optimal.recovery." (RamRecoverCertificate.recover 0)
def infeasibleRecovery : Com := isolated "infeasible.recovery." (RamRecoverCertificate.recover 1)
def unboundedRecovery : Com := isolated "unbounded.recovery." (RamRecoverCertificate.recover 2)

/-- The failed optimal and infeasibility queries leave the unbounded family
as the feasible certificate system, by the proved certificate alternative. -/
def afterInfeasible : Com := .ite RamBisectionCommit.condition infeasibleRecovery
  (.seq RamCertificateSetup.restore (.seq unboundedSystem unboundedRecovery))

def afterOptimal : Com := .ite RamBisectionCommit.condition optimalRecovery
  (.seq RamCertificateSetup.restore (.seq infeasibleSystem (.seq infeasibleDecision afterInfeasible)))

def chooseCertificate : Com := .seq optimalSystem (.seq optimalDecision afterOptimal)

/-- One fixed command decodes and clears denominators, saves the original LP,
selects a feasible certificate system, recovers its exact point, and emits the
canonical output certificate. All loops use runtime dimensions and data. -/
def solve : Com := .seq RamSolverFrontEnd.frontEnd
  (.ite (.eq (.var "input.valid") (.lit 1)) (.seq RamCertificateSetup.save chooseCertificate) .skip)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem saved_dimension_preserved : "certificate.m" ∉ chooseCertificate.wvars ∧
    "certificate.n" ∉ chooseCertificate.wvars ∧ "certificate.bits" ∉ chooseCertificate.wvars ∧
    "certificate.parameter" ∉ chooseCertificate.wvars ∧ "system.H" ∉ chooseCertificate.wvars := by
  simp only [chooseCertificate, optimalSystem, infeasibleSystem, unboundedSystem, optimalDecision,
    infeasibleDecision, optimalRecovery, infeasibleRecovery, unboundedRecovery,
    afterOptimal, afterInfeasible, isolated, RamCertificateArrayRelabel.command_wvars,
    RamCertificateDecision.decide_wvars, Com.wvars]
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem optimal_stored_system_preserved :
    "optimal.recovery.system.A.s" ∉ optimalDecision.warrs ∧
    "optimal.recovery.system.A.n" ∉ optimalDecision.warrs ∧
    "optimal.recovery.system.A.d" ∉ optimalDecision.warrs ∧
    "optimal.recovery.system.b.s" ∉ optimalDecision.warrs ∧
    "optimal.recovery.system.b.n" ∉ optimalDecision.warrs ∧
    "optimal.recovery.system.b.d" ∉ optimalDecision.warrs := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem infeasible_stored_system_preserved :
    "infeasible.recovery.system.A.s" ∉ infeasibleDecision.warrs ∧
    "infeasible.recovery.system.A.n" ∉ infeasibleDecision.warrs ∧
    "infeasible.recovery.system.A.d" ∉ infeasibleDecision.warrs ∧
    "infeasible.recovery.system.b.s" ∉ infeasibleDecision.warrs ∧
    "infeasible.recovery.system.b.n" ∉ infeasibleDecision.warrs ∧
    "infeasible.recovery.system.b.d" ∉ infeasibleDecision.warrs := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem original_coefficients_preserved :
    "source.A.s" ∉ chooseCertificate.warrs ∧ "source.A.n" ∉ chooseCertificate.warrs ∧
    "source.A.d" ∉ chooseCertificate.warrs ∧ "source.b.s" ∉ chooseCertificate.warrs ∧
    "source.b.n" ∉ chooseCertificate.warrs ∧ "source.b.d" ∉ chooseCertificate.warrs ∧
    "source.c.s" ∉ chooseCertificate.warrs ∧ "source.c.n" ∉ chooseCertificate.warrs ∧
    "source.c.d" ∉ chooseCertificate.warrs := by decide

end Lax109476Proofs.RamExactSolverProgram
