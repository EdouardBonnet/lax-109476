import Lax109476Proofs.RamCoordinateCap
import Lax109476Proofs.NormalizedFeasibility

namespace Lax109476Proofs.RamFeasibilityScales

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamFrame RamBitLength IntegerCertificates NormalizedFeasibility EllipsoidSequence

def magnitude (m n H : ℕ) : ℕ :=
  let C := coordinateCap m n H
  let G := m * C + n * m * H * C
  let D := precisionDenominator m n H
  let R := outerScale n C
  let Z := ballDenominator m n H
  let E := ballExponent m n H
  m + n + H + C + m * C + n * m + n * m * H + n * m * H * C + G + (G + 1) +
    D + (n + 1) + (C + 1) + 4 * (n + 1) + R + n * H + (n * H + 1) +
    D * (n * H + 1) + Z + E + E * n + (E * n + 1) +
    thresholdSteps n E + (thresholdSteps n E + 1) + 20

def prepareScales : Com := .seq
  (.assign "cap.G" (.add (.mul (.var "query.m") (.var "cap.value"))
    (.mul (.mul (.mul (.var "query.n") (.var "query.m")) (.var "cap.H")) (.var "cap.value"))))
  (.seq (.assign "cap.D" (.mul (.lit 2) (.add (.var "cap.G") (.lit 1))))
    (.seq (.assign "cap.R" (.mul (.mul (.lit 4) (.add (.var "query.n") (.lit 1)))
      (.add (.var "cap.value") (.lit 1))))
      (.seq (.assign "cap.ball" (.mul (.mul (.var "cap.D")
        (.add (.mul (.var "query.n") (.var "cap.H")) (.lit 1))) (.var "cap.R")))
        (.seq (.assign "bits.v" (.var "cap.ball"))
          (.seq bitLength (.seq (.assign "cap.E" (.var "bits.k"))
            (.assign "search.budget" (.add (.mul (.mul (.lit 4) (.add (.var "query.n") (.lit 1)))
              (.add (.mul (.var "cap.E") (.var "query.n")) (.lit 1))) (.lit 1)))))))))

def Output (m n H : ℕ) (σ : Env) : Prop :=
  σ.vars "cap.D" = precisionDenominator m n H ∧
    σ.vars "cap.R" = outerScale n (coordinateCap m n H) ∧
    σ.vars "cap.E" = ballExponent m n H ∧
    σ.vars "search.budget" = thresholdSteps n (ballExponent m n H) + 1 ∧
    σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "cap.H" = H

set_option maxHeartbeats 800000 in
theorem prepareScales_spec (B m n H : ℕ) (hB : magnitude m n H < B) :
    Spec B (fun σ => σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧
        σ.vars "cap.H" = H ∧ σ.vars "cap.value" = coordinateCap m n H)
      prepareScales (fun _ τ => Output m n H τ) (12 * (ballExponent m n H) + 62) := by
  let C := coordinateCap m n H
  let G := m * C + n * m * H * C
  let D := precisionDenominator m n H
  let R := outerScale n C
  let Z := ballDenominator m n H
  let E := ballExponent m n H
  have h2 : 2 < B := by dsimp [magnitude] at hB; omega
  have hD : D = 2 * (G + 1) := rfl
  have hR : R = 4 * (n + 1) * (C + 1) := rfl
  have hZ : Z = D * (n * H + 1) * R := rfl
  have hE : E = Z.size := rfl
  have hZB : Z < B := by dsimp [Z, magnitude] at hB ⊢; omega
  have hlength := spec_with_fields ["cap.D", "cap.R", "cap.value", "cap.H", "query.m", "query.n"]
    (bitLength_spec B Z h2 hZB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rfl)
  rintro σ ⟨hσm, hσn, hσH, hσC⟩
  run_vcg [hlength]
  all_goals clear hlength
  all_goals simp_all [Output, FieldsAgree, C, G, D, R, Z, E, hD, hR, hZ, hE,
    ballExponent, ballDenominator, precisionDenominator, Relaxation.relaxationDenominator,
    outerScale, thresholdSteps]
  all_goals dsimp [magnitude, ballExponent, ballDenominator, precisionDenominator,
    Relaxation.relaxationDenominator, outerScale, thresholdSteps] at hB
  all_goals omega

end Lax109476Proofs.RamFeasibilityScales
