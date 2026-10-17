import PfaffianDescent.ActualModuleOpenPointSectionClass
import PfaffianDescent.ActualPositiveTwoOverlapBasisSection

/- SOURCE ONLY / UNVERIFIED. The actual O(2) generators, in the SAME
original point fiber, differ by the square of the actual overlap ratio.
The transition is derived from literal localization section values. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite HomogeneousLocalization
open AllCharacteristics.GradedChart ProjectiveNegativeTwist
universe u

lemma actualPositiveTwo_commonOpen_point_basis_transition
    {K L A : Type u} [Field K] [Field L] [CommRing A] [Algebra K A]
    (G : ℕ → Submodule K A) [GradedRing G]
    {f h : A} (hf : f ∈ G 1) (hh : h ∈ G 1)
    (g : Proj G ⟶ Spec (.of K))
    (q : Spec (.of L) ⟶ (Proj.basicOpen G (f * h) : Scheme)) :
    let W := Proj.basicOpen G (f * h)
    let ratio := (Proj.awayToSection G (f * h)).hom
      (awayMap G hh rfl (normalized G hf h hh))
    let f2 : G 2 := ⟨f ^ 2, by simpa using pow_mem_graded 2 hf⟩
    let h2 : G 2 := ⟨h ^ 2, by simpa using pow_mem_graded 2 hh⟩
    actualModuleOpenPointSectionClass g W q (positiveSheafOfModules G 2)
        ((positiveGlobalSectionOfHomogeneous G 2 h2).val (op W)) =
      actualOpenPointResidue W q ratio ^ 2 •
        actualModuleOpenPointSectionClass g W q (positiveSheafOfModules G 2)
          ((positiveGlobalSectionOfHomogeneous G 2 f2).val (op W)) := by
  dsimp only
  rw [← actualPositiveTwo_overlap_basis_section G hf hh,
    actualModuleOpenPointSectionClass_smul, map_pow]

end PfaffianDescent
