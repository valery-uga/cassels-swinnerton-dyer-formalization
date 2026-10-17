import PfaffianDescent.AffineTraceSelectedQuotientAndJet
import PfaffianDescent.ActualDualMorphismDifferentialFiberLine

/- SOURCE ONLY / UNVERIFIED. The SAME trace quotient's tangent v defines
an ACTUAL hypersurface algebra quotient. Its genuine Kaehler line has the
literal same quadric values, proved through the epsilon derivation. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open scoped TensorProduct
universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
    (b : Basis (Fin 4) K L) (F : AffineThreeRing K)
    (hpoint : MvPolynomial.aeval (fun i : Fin 3 => b i.succ) F = 0)

def affineTraceQuotientHypersurfaceJet
    (q : Module.Dual L (LinearMap.ker
      (affineDifferential (fun i : Fin 3 => b i.succ) F)) →ₗ[L] L) :
    (AffineThreeRing K ⧸ Ideal.span {F}) →ₐ[K] DualNumber L := by
  let p := fun i : Fin 3 => b i.succ
  let T := LinearMap.ker (affineDifferential p F)
  let v : T := (Module.evalEquiv L T).symm q
  have hjet : affineFirstJet p v.val F = 0 :=
    (affineFirstJet_eq_zero_iff p v.val F).mpr ⟨hpoint, v.property⟩
  exact affineHypersurfaceJet p v.val F hjet

lemma affineTraceQuotientHypersurfaceJet_quadric_snd
    (q : Module.Dual L (LinearMap.ker
      (affineDifferential (fun i : Fin 3 => b i.succ) F)) →ₗ[L] L)
    (Q : affineQuadricsThroughPoint (k := K) (fun i : Fin 3 => b i.succ)) :
    (affineTraceQuotientHypersurfaceJet b F hpoint q
      (Ideal.Quotient.mk (Ideal.span {F}) (affineQuadrics Q.val))).snd =
        q (affineQuadricCotangentRestriction (fun i : Fin 3 => b i.succ) F Q) := by
  let p := fun i : Fin 3 => b i.succ
  let T := LinearMap.ker (affineDifferential p F)
  let v : T := (Module.evalEquiv L T).symm q
  change (affineFirstJet p v.val (affineQuadrics Q.val)).snd = _
  have he : (affineQuadricCotangentRestriction p F Q) v =
      q (affineQuadricCotangentRestriction p F Q) :=
    Module.apply_evalEquiv_symm_apply L T (affineQuadricCotangentRestriction p F Q) q
  simpa only [affineQuadricCotangentRestriction, LinearMap.domRestrict_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.domRestrict'_apply,
    affineDifferentialMap, affineFirstJet_snd, affineDifferential] using he

/-- The line on the genuine hypersurface Kaehler fiber is internally derived
from the very SAME actual algebra map. No desired line/jet equation is input. -/
theorem affineTraceQuotientHypersurfaceJet_kaehler_quadric
    (q : Module.Dual L (LinearMap.ker
      (affineDifferential (fun i : Fin 3 => b i.succ) F)) →ₗ[L] L)
    (Q : affineQuadricsThroughPoint (k := K) (fun i : Fin 3 => b i.succ)) :
    let R := AffineThreeRing K ⧸ Ideal.span {F}
    let phi := affineTraceQuotientHypersurfaceJet b F hpoint q
    let rho := actualDualQuotientResidue phi
    letI : Algebra R L := rho.toRingHom.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (rho.commutes c).symm)
    actualDualMorphismDifferentialFiberLine phi
      ((1 : L) ⊗ₜ[R] KaehlerDifferential.D K R
        (Ideal.Quotient.mk (Ideal.span {F}) (affineQuadrics Q.val))) =
      q (affineQuadricCotangentRestriction (fun i : Fin 3 => b i.succ) F Q) := by
  dsimp only
  rw [actualDualMorphismDifferentialFiberLine_tmul_D, one_mul]
  exact affineTraceQuotientHypersurfaceJet_quadric_snd b F hpoint q Q

lemma affineTraceQuotientHypersurfaceJet_surjective
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hb : b 0 = 1)
    (q : Module.Dual L (LinearMap.ker
      (affineDifferential (fun i : Fin 3 => b i.succ) F)) →ₗ[L] L)
    (hq : Function.Surjective q) :
    Function.Surjective (affineTraceQuotientHypersurfaceJet b F hpoint q) := by
  let p := fun i : Fin 3 => b i.succ
  let T := LinearMap.ker (affineDifferential p F)
  let v : T := (Module.evalEquiv L T).symm q
  have hv : v.val ≠ 0 := by
    intro hz
    have hvzero : v = 0 := Subtype.ext hz
    obtain ⟨x, hx⟩ := hq 1
    have he : x v = q x := Module.apply_evalEquiv_symm_apply L T x q
    rw [hvzero, map_zero, hx] at he
    exact zero_ne_one he
  exact affineHypersurfaceJet_surjective p v.val F
    (affineResidueEvaluation_surjective b hb) hv _

end PfaffianDescent.QuarticNet
