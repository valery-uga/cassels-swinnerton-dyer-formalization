import PfaffianDescent.FiniteFlatHilbertTestPoints195
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! SOURCE ONLY314. Genuine geometric open-chart locus for an ORIGINAL
whole finite-flat family. Its bad locus has closed image by finiteness;
on the derived good base open the entire source scheme factors into the
chosen ambient open. No Hilbert representation or support/transition
certificate is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ)
variable (P : FiniteFlatHilbertPoint195 F n) (U : X.Opens)

include P U in
def finiteFamilyWholeOpenLocus314 : B.Opens := by
  letI : IsFinite (P.val.subschemeι ≫ F) := P.property.1
  exact ⟨((P.val.subschemeι ≫ F) '' ((P.val.subschemeι ⁻¹ᵁ U :
    P.val.subscheme.Opens) : Set P.val.subscheme)ᶜ)ᶜ,
    ((P.val.subschemeι ≫ F).isClosedMap _
      (P.val.subschemeι ⁻¹ᵁ U).isOpen.isClosed_compl).isOpen_compl⟩

/-- Exact whole-fiber condition; no reduction/reducedness assumption. -/
lemma mem_finiteFamilyWholeOpenLocus_iff314 (b : B) :
    b ∈ finiteFamilyWholeOpenLocus314 F n P U ↔
      ∀ z : P.val.subscheme, (P.val.subschemeι ≫ F) z = b → P.val.subschemeι z ∈ U := by
  classical
  change b ∉ (P.val.subschemeι ≫ F) '' {z | P.val.subschemeι z ∉ U} ↔ _
  constructor
  · intro hb z hz
    by_contra hU
    exact hb ⟨z, hU, hz⟩
  · intro hb
    rintro ⟨z, hz, hzb⟩
    exact hz (hb z hzb)

/-- This is the maximal actual base open on which every fiber lies in U. -/
lemma finiteFamilyWholeOpenLocus_maximal314 (V : B.Opens) :
    V ≤ finiteFamilyWholeOpenLocus314 F n P U ↔
      ∀ z : P.val.subscheme, (P.val.subschemeι ≫ F) z ∈ V → P.val.subschemeι z ∈ U := by
  constructor
  · intro h z hz
    exact (mem_finiteFamilyWholeOpenLocus_iff314 F n P U _).mp (h hz) z rfl
  · intro h b hb
    apply (mem_finiteFamilyWholeOpenLocus_iff314 F n P U b).mpr
    intro z hz
    exact h z (hz.symm ▸ hb)

include P U in
def finiteFamilyWholeOpenSource314 : P.val.subscheme.Opens :=
  (P.val.subschemeι ≫ F) ⁻¹ᵁ finiteFamilyWholeOpenLocus314 F n P U

lemma finiteFamilyWholeOpenSource_range_in_chart314 :
    Set.range ((finiteFamilyWholeOpenSource314 F n P U).ι ≫ P.val.subschemeι) ⊆
      Set.range U.ι := by
  rintro _ ⟨z, rfl⟩
  rw [U.range_ι]
  change P.val.subschemeι z.val ∈ U
  have hz : (P.val.subschemeι ≫ F) z.val ∈ finiteFamilyWholeOpenLocus314 F n P U := z.property
  exact (mem_finiteFamilyWholeOpenLocus_iff314 F n P U _).mp hz z.val rfl

/-- Actual map of the ENTIRE restricted source scheme into original U,
derived by the open immersion universal property. -/
def finiteFamilyWholeOpenChartLift314 :
    (finiteFamilyWholeOpenSource314 F n P U).toScheme ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι
    ((finiteFamilyWholeOpenSource314 F n P U).ι ≫ P.val.subschemeι)
    (finiteFamilyWholeOpenSource_range_in_chart314 F n P U)

lemma finiteFamilyWholeOpenChartLift_comp314 :
    finiteFamilyWholeOpenChartLift314 F n P U ≫ U.ι =
      (finiteFamilyWholeOpenSource314 F n P U).ι ≫ P.val.subschemeι :=
  IsOpenImmersion.lift_fac _ _ _

/-- Native base-change projection of the SAME original entire family. -/
def finiteFamilyWholeOpenProjection314 :
    (finiteFamilyWholeOpenSource314 F n P U).toScheme ⟶
      (finiteFamilyWholeOpenLocus314 F n P U).toScheme :=
  (P.val.subschemeι ≫ F) ∣_ finiteFamilyWholeOpenLocus314 F n P U

lemma finiteFamilyWholeOpenProjection_isPullback314 :
    IsPullback (finiteFamilyWholeOpenSource314 F n P U).ι
      (finiteFamilyWholeOpenProjection314 F n P U) (P.val.subschemeι ≫ F)
      (finiteFamilyWholeOpenLocus314 F n P U).ι :=
  (isPullback_morphismRestrict (P.val.subschemeι ≫ F)
    (finiteFamilyWholeOpenLocus314 F n P U)).flip

lemma finiteFamilyWholeOpenProjection_finite314 :
    IsFinite (finiteFamilyWholeOpenProjection314 F n P U) := by
  letI : IsFinite (P.val.subschemeι ≫ F) := P.property.1
  exact MorphismProperty.of_isPullback (finiteFamilyWholeOpenProjection_isPullback314 F n P U)
    (inferInstance : IsFinite (P.val.subschemeι ≫ F))

lemma finiteFamilyWholeOpenProjection_flat314 :
    Flat (finiteFamilyWholeOpenProjection314 F n P U) := by
  letI : Flat (P.val.subschemeι ≫ F) := P.property.2.1
  exact MorphismProperty.of_isPullback (finiteFamilyWholeOpenProjection_isPullback314 F n P U)
    (inferInstance : Flat (P.val.subschemeι ≫ F))

lemma finiteFamilyWholeOpenProjection_finrank314
    (b : (finiteFamilyWholeOpenLocus314 F n P U).toScheme) :
    (finiteFamilyWholeOpenProjection314 F n P U).finrank b = n := by
  letI : IsFinite (P.val.subschemeι ≫ F) := P.property.1
  letI : Flat (P.val.subschemeι ≫ F) := P.property.2.1
  exact (Scheme.Hom.finrank_of_isPullback (finiteFamilyWholeOpenSource314 F n P U).ι
    (finiteFamilyWholeOpenProjection314 F n P U) (P.val.subschemeι ≫ F)
    (finiteFamilyWholeOpenLocus314 F n P U).ι
    (finiteFamilyWholeOpenProjection_isPullback314 F n P U) b).trans
      (P.property.2.2 ((finiteFamilyWholeOpenLocus314 F n P U).ι b))

/-- SAME chart lift retains the original map to the good base; not merely a
pointwise support inclusion. -/
lemma finiteFamilyWholeOpenChartLift_toBase314 :
    finiteFamilyWholeOpenChartLift314 F n P U ≫ (U.ι ≫ F) =
      finiteFamilyWholeOpenProjection314 F n P U ≫ (finiteFamilyWholeOpenLocus314 F n P U).ι :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ F) (finiteFamilyWholeOpenChartLift_comp314 F n P U)).trans
      ((Category.assoc _ _ _).trans
        (morphismRestrict_ι (P.val.subschemeι ≫ F)
          (finiteFamilyWholeOpenLocus314 F n P U)).symm))

end PfaffianDescent
end
