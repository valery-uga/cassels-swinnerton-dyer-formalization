import PfaffianDescent.LengthTwoLocalDualClassification
import PfaffianDescent.QuarticInfinitesimalPoints
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.LinearAlgebra.Dimension.Free

/-! A supplied finite local rank-eight ground algebra with separable
quartic residue is itself a dual-number algebra. Its coefficient field is
LIFTED internally through the actual nilpotent residue kernel. -/

noncomputable section
namespace PfaffianDescent
open Module Algebra
universe u
variable {k L A : Type u} [Field k] [Field L] [CommRing A]
  [Algebra k L] [Algebra k A] [FiniteDimensional k L]
  [FiniteDimensional k A] [Algebra.IsSeparable k L] [IsLocalRing A]

private theorem finiteLocal_residueKernel_nilpotent
    (rho : A →ₐ[k] L) (hrho : Function.Surjective rho) :
    IsNilpotent (RingHom.ker rho.toRingHom) := by
  letI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  rw [IsLocalRing.ker_eq_maximalIdeal rho.toRingHom hrho]
  exact (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance

/-- Every separable residue field has a unique coefficient-field section
inside the GIVEN finite local algebra. No section certificate is supplied. -/
theorem finiteLocal_separable_residue_has_unique_section
    (rho : A →ₐ[k] L) (hrho : Function.Surjective rho) :
    ∃! s : L →ₐ[k] A, rho.comp s = AlgHom.id k L := by
  letI : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  have hnil := finiteLocal_residueKernel_nilpotent rho hrho
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k L) rho hrho hnil
  have hs : rho.comp s = AlgHom.id k L :=
    Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k L) rho hrho hnil
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact Algebra.FormallyUnramified.lift_unique' rho hnil t s (ht.trans hs.symm)

/-- This classification is universal for the actual local algebra, unlike a
construction of some possibly different length-eight subscheme. -/
theorem lengthEightLocal_quarticResidue_dual_equiv_with_residue
    (rho : A →ₐ[k] L) (hrho : Function.Surjective rho)
    (hL : finrank k L = 4) (hA : finrank k A = 8) :
    ∃ e : DualNumber L ≃ₐ[k] A, ∀ z, rho (e z) = z.fst := by
  obtain ⟨s, hs, _⟩ := finiteLocal_separable_residue_has_unique_section rho hrho
  letI : Algebra L A := s.toRingHom.toAlgebra
  letI : IsScalarTower k L A := IsScalarTower.of_algebraMap_eq
    (fun c => (s.commutes c).symm)
  letI : Module.Finite L A := Module.Finite.of_restrictScalars_finite k L A
  have hLA : finrank L A = 2 := by
    have h := Module.finrank_mul_finrank k L A
    rw [hL, hA] at h
    omega
  let rhoL : A →ₐ[L] L :=
    { rho.toRingHom with
      commutes' := fun c => by
        change rho (s c) = c
        exact AlgHom.congr_fun hs c }
  obtain ⟨e⟩ := lengthTwoLocal_dual_equiv_of_rational_residue rhoL hLA
  have heps : rhoL (e (DualNumber.eps : DualNumber L)) = 0 := by
    have hsq : rhoL (e (DualNumber.eps : DualNumber L)) *
        rhoL (e (DualNumber.eps : DualNumber L)) = 0 := by
      rw [← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]
    exact (mul_eq_zero.mp hsq).elim id id
  have hcomp : rhoL.comp e.toAlgHom = TrivSqZeroExt.fstHom L L L := by
    apply DualNumber.algHom_ext
    change rhoL (e (DualNumber.eps : DualNumber L)) = 0
    exact heps
  refine ⟨e.restrictScalars k, ?_⟩
  intro z
  exact AlgHom.congr_fun hcomp z

theorem lengthEightLocal_quarticResidue_dual_equiv
    (rho : A →ₐ[k] L) (hrho : Function.Surjective rho)
    (hL : finrank k L = 4) (hA : finrank k A = 8) :
    Nonempty (DualNumber L ≃ₐ[k] A) := by
  obtain ⟨e, _⟩ := lengthEightLocal_quarticResidue_dual_equiv_with_residue rho hrho hL hA
  exact ⟨e⟩

/-- Every supplied affine coordinate presentation of the actual ground
rank-eight algebra extracts its OWN nonzero ground tangent jet. -/
theorem lengthEightLocal_actual_affine_jet
    (rho : A →ₐ[k] L) (hrho : Function.Surjective rho)
    (hL : finrank k L = 4) (hA : finrank k A = 8)
    (f : MvPolynomial (Fin 3) k →ₐ[k] A) (hf : Function.Surjective f) :
    ∃ (e : A ≃ₐ[k] DualNumber L) (p v : Fin 3 → L), v ≠ 0 ∧
      e.toAlgHom.comp f = QuarticNet.affineFirstJet p v ∧
      (∀ i, p i = rho (f (MvPolynomial.X i))) := by
  obtain ⟨e0, he0⟩ := lengthEightLocal_quarticResidue_dual_equiv_with_residue rho hrho hL hA
  let e := e0.symm
  let phi : MvPolynomial (Fin 3) k →ₐ[k] DualNumber L := e.toAlgHom.comp f
  let p : Fin 3 → L := fun i => (phi (MvPolynomial.X i)).fst
  let v : Fin 3 → L := fun i => (phi (MvPolynomial.X i)).snd
  have hjet : phi = QuarticNet.affineFirstJet p v := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [QuarticNet.affineFirstJet, MvPolynomial.aeval_X]
    apply TrivSqZeroExt.ext <;> simp [p, v]
  have hv : v ≠ 0 := by
    intro hv0
    have hsnd (i : Fin 3) : (phi (MvPolynomial.X i)).snd = 0 := congrFun hv0 i
    have hconstant : phi = (TrivSqZeroExt.inlAlgHom k L L).comp (MvPolynomial.aeval p) := by
      apply MvPolynomial.algHom_ext
      intro i
      apply TrivSqZeroExt.ext <;> simp [p, hsnd]
    have hsurj : Function.Surjective phi := e.surjective.comp hf
    obtain ⟨q, hq⟩ := hsurj (TrivSqZeroExt.inr (1 : L))
    rw [hconstant] at hq
    have h := congrArg TrivSqZeroExt.snd hq
    exact (zero_ne_one : (0 : L) ≠ 1) (by simpa using h)
  refine ⟨e, p, v, hv, hjet, ?_⟩
  intro i
  have h := he0 (e (f (MvPolynomial.X i)))
  simpa [e, p, phi] using h.symm

/-- The reconstructed tangent jet has exactly the given ambient quotient
kernel; equality holds for all polynomials, hence also for the full quadratic
linear system. -/
theorem lengthEightLocal_actual_affine_jet_kernel
    (rho : A →ₐ[k] L) (hrho : Function.Surjective rho)
    (hL : finrank k L = 4) (hA : finrank k A = 8)
    (f : MvPolynomial (Fin 3) k →ₐ[k] A) (hf : Function.Surjective f) :
    ∃ p v : Fin 3 → L, v ≠ 0 ∧
      RingHom.ker f.toRingHom = RingHom.ker (QuarticNet.affineFirstJet p v).toRingHom ∧
      (∀ i, p i = rho (f (MvPolynomial.X i))) := by
  obtain ⟨e, p, v, hv, he, hp⟩ :=
    lengthEightLocal_actual_affine_jet rho hrho hL hA f hf
  refine ⟨p, v, hv, ?_, hp⟩
  ext q
  change f q = 0 ↔ QuarticNet.affineFirstJet p v q = 0
  rw [← he]
  exact ⟨fun h => by simp [h], fun h => e.injective (by simpa using h)⟩

end PfaffianDescent
