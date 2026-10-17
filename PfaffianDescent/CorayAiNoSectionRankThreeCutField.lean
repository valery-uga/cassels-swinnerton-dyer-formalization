import AllCharacteristics.FiniteFlatCycle
import AllCharacteristics.SchemeQuadraticDescent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The ENTIRE original-K rank-three affine closed cut of a cubic with no
rational section is a FIELD. Actual nilpotents are proved absent; no radical
replacement or chosen residue-field model is substituted for the cut. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- No-section and actual whole-cut rank3 force the actual cut algebra to
be a field. Every maximal quotient of smaller rank would construct an
original degree1/2 effective cycle and hence a rational cubic section. -/
theorem cubic_noSection_rankThree_affineClosedCut_isField001
    {K B : Type u} [Field K] [CommRing B] [Algebra K B] [Module.Finite K B]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (i : Spec (.of B) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hbase : i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K B)))
    (hrank : finrank K B = 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) : IsField B := by
  classical
  letI : Nontrivial B := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank K B)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := B)
  letI : m.IsMaximal := hm
  let L := B ⧸ m
  letI : Field L := Ideal.Quotient.field m
  letI : Module.Finite K L := inferInstance
  let ev : B →ₐ[K] L := Ideal.Quotient.mkₐ K m
  have hev : Function.Surjective ev := Ideal.Quotient.mk_surjective
  have hLe : finrank K L ≤ 3 :=
    (LinearMap.finrank_le_finrank_of_surjective (f := ev.toLinearMap) hev).trans_eq hrank
  have hPositive : 0 < finrank K L := Module.finrank_pos
  have hNotSmall : ¬ finrank K L ≤ 2 := by
    intro hSmall
    let j : Spec (.of L) ⟶ Spec (.of B) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))
    letI : IsClosedImmersion j := IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of B) m
    let k := j ≫ i
    have hLbase : k ≫ hypersurfaceToBase p hp =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
      dsimp only [k, j]
      rw [Category.assoc, hbase, ← Spec.map_comp]
      rfl
    letI : IsFinite (k ≫ hypersurfaceToBase p hp) := by
      rw [hLbase]
      exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
    obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_closed_subscheme k
      (hypersurfaceToBase p hp)
    have hRankL : finiteSchemeRank (k ≫ hypersurfaceToBase p hp) = finrank K L := by
      rw [finiteSchemeRank_eq_finrank, hLbase, Scheme.Hom.finrank_SpecMap_algebraMap]
      exact (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := L)) _)
    have hzL : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = finrank K L :=
      hz.trans hRankL
    apply hno
    apply hypersurface_section_of_effective_cycle_degree_one_or_two p hp z
    omega
  have hDimL : finrank K L = 3 := by omega
  have hInjective : Function.Injective ev :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hrank.trans hDimL.symm)
      (f := ev.toLinearMap)).mpr hev
  have hmBot : m = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    apply hInjective
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr hx).trans (map_zero ev).symm
  apply Ring.isField_iff_maximal_bot.mpr
  rw [← hmBot]
  exact hm

end PfaffianDescent.Coray
