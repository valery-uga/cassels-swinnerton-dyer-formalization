import PfaffianDescent.QuadraticFullBaseLocusInfiniteExtension
import PfaffianDescent.HomogeneousFrameBaseChange

/-! Scalar extension preserves the dimension of the entire quadratic system.
This is a dimension-descent primitive, not an assumed dimension-three or
quadratic-generation certificate.  Evaluation compatibility retains equations
in arbitrary coefficient algebras, including their nilpotents. -/

noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
open AllCharacteristics.UniversalHomogeneous
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem quadraticSystemCoefficientExtension_finrank
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (hW : ∀ p ∈ W, p.IsHomogeneous 2) :
    Module.finrank L (quadraticSystemCoefficientExtension (L := L) W) =
      Module.finrank K W := by
  let H := homogeneousSubmodule (Fin 4) K 2
  letI : Module.Finite K H :=
    (Submodule.fg_iff_finiteDimensional H).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) K 2)
  let f : W →ₗ[K] H :=
    { toFun := fun p => ⟨p.val, hW p.val p.property⟩
      map_add' := by intro p q; rfl
      map_smul' := by intro a p; rfl }
  have hf : Function.Injective f := by
    intro p q hpq
    exact Subtype.ext (congrArg Subtype.val hpq)
  letI : Module.Finite K W := Module.Finite.of_injective f hf
  let b := Module.finBasis K W
  let frame := fun i => f (b i)
  have hframe : LinearIndependent K frame :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  let e : Fin (Fintype.card (Monomials (Fin 4) 2)) ≃ Monomials (Fin 4) 2 :=
    (Fintype.equivFin _).symm
  have hLI := homogeneousFrame_baseChange_linearIndependent
    (K := K) (L := L) e frame hframe
  let mapped := fun i => MvPolynomial.map (algebraMap K L) (b i).val
  have hLIpoly : LinearIndependent L mapped := by
    exact hLI.map' (homogeneousSubmodule (Fin 4) L 2).subtype
      (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _))
  have hspan : quadraticSystemCoefficientExtension (L := L) W =
      Submodule.span L (Set.range mapped) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro p ⟨p₀, hp₀, rfl⟩
      let w : W := ⟨p₀, hp₀⟩
      have hrepr := congrArg
        (fun v : W => MvPolynomial.map (algebraMap K L) v.val) (b.sum_repr w)
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum,
        smul_eq_C_mul, map_mul, map_C] at hrepr
      rw [← hrepr]
      apply Submodule.sum_mem
      intro i _
      simpa only [smul_eq_C_mul] using
        Submodule.smul_mem (Submodule.span L (Set.range mapped))
          (algebraMap K L (b.repr w i))
          (Submodule.subset_span (Set.mem_range_self i))
    · apply Submodule.span_le.mpr
      rintro p ⟨i, rfl⟩
      exact Submodule.subset_span ⟨(b i).val, (b i).property, rfl⟩
  rw [hspan, finrank_span_eq_card hLIpoly, Fintype.card_fin]

section Evaluation
variable {A B : Type u} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] [Algebra L B] [IsScalarTower K L B]

/-- Extending polynomial coefficients and the coordinate algebra preserves
literal zero evaluation.  In particular this applies to B = L ⊗[K] A. -/
theorem quadraticSystemCoefficientExtension_evaluation_zero
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (x : Fin 4 → A) (φ : A →ₐ[K] B)
    (hzero : ∀ p ∈ W, p.eval₂ (algebraMap K A) x = 0) :
    ∀ p ∈ quadraticSystemCoefficientExtension (L := L) W,
      p.eval₂ (algebraMap L B) (fun j => φ (x j)) = 0 := by
  let ev : MvPolynomial (Fin 4) L →ₐ[L] B :=
    MvPolynomial.aeval (fun j => φ (x j))
  have hle : quadraticSystemCoefficientExtension (L := L) W ≤
      LinearMap.ker ev.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro p ⟨p₀, hp₀, rfl⟩
    change (p₀.map (algebraMap K L)).eval₂ (algebraMap L B)
      (fun j => φ (x j)) = 0
    have hcoeff : (algebraMap L B).comp (algebraMap K L) =
        φ.toRingHom.comp (algebraMap K A) := by
      ext a
      exact (IsScalarTower.algebraMap_apply K L B a).symm.trans (φ.commutes a).symm
    rw [eval₂_map, hcoeff, ← hom_eval₂, hzero p₀ hp₀, map_zero]
  exact fun p hp => hle hp

end Evaluation
end PfaffianDescent
