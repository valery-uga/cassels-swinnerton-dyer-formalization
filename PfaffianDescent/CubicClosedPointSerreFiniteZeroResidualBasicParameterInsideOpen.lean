import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualBasicParameterRing
import Mathlib.AlgebraicGeometry.OpenImmersion

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_basicParameterMap
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : Spec R ⟶ X) (t : R) :
    Spec (.of (Localization.Away t)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t))) ≫ j

instance cubicClosedPointSerreFiniteZeroResidual_basicParameterMap_isOpenImmersion
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j] (t : R) :
    IsOpenImmersion (cubicClosedPointSerreFiniteZeroResidual_basicParameterMap j t) := by
  dsimp [cubicClosedPointSerreFiniteZeroResidual_basicParameterMap]
  infer_instance

/-- At every point of an actual parameter open, a nonzero principal chart
of the chosen native affine chart lies inside that parameter open. -/
theorem cubicClosedPointSerreFiniteZeroResidual_basicParameter_inside_open
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : Spec R ⟶ X)
    (V : X.Opens) (y : Spec R) (hy : j y ∈ V) :
    ∃ t : R, t ≠ 0 ∧ ∃ z : Spec (.of (Localization.Away t)),
      cubicClosedPointSerreFiniteZeroResidual_basicParameterMap j t z = j y ∧
        Set.range (cubicClosedPointSerreFiniteZeroResidual_basicParameterMap j t) ⊆ V := by
  have hopen : IsOpen (j ⁻¹' (V : Set X)) := V.2.preimage j.continuous
  obtain ⟨_, ⟨t, rfl⟩, hyt, htV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hopen y hy
  have ht0 : t ≠ 0 := by
    intro ht
    simpa [ht] using hyt
  let m : Spec (.of (Localization.Away t)) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))
  have hm : Set.range m = (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away t) t
  have hy' : y ∈ Set.range m := by rw [hm]; exact hyt
  obtain ⟨z, hz⟩ := hy'
  refine ⟨t, ht0, z, ?_, ?_⟩
  · change j (m z) = j y
    rw [hz]
  · rw [cubicClosedPointSerreFiniteZeroResidual_basicParameterMap, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp]
    change j '' Set.range m ⊆ V
    rw [hm]
    exact Set.image_subset_iff.mpr htV

end PfaffianDescent
