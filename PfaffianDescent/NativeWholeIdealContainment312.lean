import PfaffianDescent.NativeAffineWholeIdealFaithfulness306
import PfaffianDescent.WholeIdealOpenCoverUniqueness

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Entire affine ideal inclusion is equivalent to inclusion of the actual
closed quotient kernels, including nilpotents. -/
lemma nativeAffineQuotientKernel_le_iff312
    {C : Type u} [CommRing C] (I J : Ideal C) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker ≤
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker ↔ I ≤ J := by
  constructor
  · intro h
    have ht := h ⟨⊤, isAffineOpen_top (Spec (.of C))⟩
    rw [nativeSpecMap_kernel_top306, nativeSpecMap_kernel_top306,
      Ideal.mk_ker, Ideal.mk_ker] at ht
    intro x hx
    obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of C)).hom).surjective x
    exact ht hx
  · intro h
    apply Scheme.IdealSheafData.le_of_isAffine
    rw [nativeSpecMap_kernel_top306, nativeSpecMap_kernel_top306,
      Ideal.mk_ker, Ideal.mk_ker]
    exact Ideal.comap_mono h

/-- Whole native containment is determined on an internally chosen actual
open cover, by whole-ideal uniqueness applied to the native supremum. -/
lemma wholeIdeal_le_of_openCover_comaps312
    {X : Scheme.{u}} (U : X.OpenCover.{u}) {I J : X.IdealSheafData}
    (h : ∀ i : U.I₀, I.comap (U.f i) ≤ J.comap (U.f i)) : I ≤ J := by
  have he : I ⊔ J = J := wholeIdeal_eq_of_openCover_comaps U (fun i => by
    rw [Scheme.IdealSheafData.comap_sup]
    exact sup_eq_right.mpr (h i))
  exact sup_eq_right.mp he

/-- Whole ideal containment is precisely the condition for an actual map to
factor through the original closed subscheme. -/
def nativeClosedSubschemeFactor312
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (h : I ≤ f.ker) :
    X ⟶ I.subscheme :=
  f.toImage ≫ Scheme.IdealSheafData.inclusion h

lemma nativeClosedSubschemeFactor_comp312
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (h : I ≤ f.ker) :
    nativeClosedSubschemeFactor312 I f h ≫ I.subschemeι = f := by
  rw [nativeClosedSubschemeFactor312, Category.assoc,
    Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]

lemma nativeClosedSubschemeFactor_existsUnique312
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (h : I ≤ f.ker) :
    ∃! a : X ⟶ I.subscheme, a ≫ I.subschemeι = f := by
  refine ⟨nativeClosedSubschemeFactor312 I f h, nativeClosedSubschemeFactor_comp312 I f h, ?_⟩
  intro a ha
  exact (cancel_mono I.subschemeι).mp
    (ha.trans (nativeClosedSubschemeFactor_comp312 I f h).symm)

lemma nativeClosedSubschemeFactor_iff312
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (∃ a : X ⟶ I.subscheme, a ≫ I.subschemeι = f) ↔ I ≤ f.ker := by
  constructor
  · rintro ⟨a, ha⟩
    have h := a.le_ker_comp I.subschemeι
    rw [I.ker_subschemeι, ha] at h
    exact h
  · intro h
    exact ⟨nativeClosedSubschemeFactor312 I f h, nativeClosedSubschemeFactor_comp312 I f h⟩

end PfaffianDescent
end
