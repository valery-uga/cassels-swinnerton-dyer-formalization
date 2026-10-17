import PfaffianDescent.AmbientPointKoszulPointPrime
import PfaffianDescent.AmbientPointKoszulSheafExactness
import PfaffianDescent.LocalExtResidueInjective

/-! # Actual augmentation and Koszul stalks away from the standard point -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

local instance ambientPointKoszul_offPointPrime (x : Proj PS) :
    (ProjectiveNegativeTwist.pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

set_option backward.isDefEq.respectTransparency false in
/-- The actual pushed-forward point structure module has zero stalk
outside the image of the actual standard-point closed immersion. -/
theorem ambientPointKoszul_pointModule_stalk_subsingleton_off_range
    (x : Proj PS) (hx : x ∉ Set.range (ambientPointKoszul_point K)) :
    Subsingleton ((schemeModuleStalkFunctor (Proj PS) x).obj (ambientPointKoszul_pointModule K)) :=
  schemeModulePushforward_stalk_subsingleton_off_range
    (ambientPointKoszul_point K) (SheafOfModules.unit (Spec (.of K)).ringCatSheaf) x hx

set_option backward.isDefEq.respectTransparency false in
/-- The three coordinate equations vanish only on the actual standard point. -/
theorem ambientPointKoszul_mem_point_range_of_coordinates
    (x : Proj PS)
    (h1 : X (1 : Fin 4) ∈ ProjectiveNegativeTwist.pointIdeal PS x)
    (h2 : X (2 : Fin 4) ∈ ProjectiveNegativeTwist.pointIdeal PS x)
    (h3 : X (3 : Fin 4) ∈ ProjectiveNegativeTwist.pointIdeal PS x) :
    x ∈ Set.range (ambientPointKoszul_point K) := by
  have hx0 : X (0 : Fin 4) ∈ (ProjectiveNegativeTwist.pointIdeal PS x).primeCompl := by
    change X (0 : Fin 4) ∉ ProjectiveNegativeTwist.pointIdeal PS x
    intro h0
    apply x.not_irrelevant_le
    apply (ProjectiveNegativeTwist.p3Coordinates_span_irrelevant K).trans
    rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  let xj : Proj.basicOpen PS (X (0 : Fin 4)) := ⟨x, hx0⟩
  let q := (ProjectiveSpectrum.Proj.toSpec PS (X (0 : Fin 4))).base xj
  have hc (i : Fin 4) (hi : X i ∈ ProjectiveNegativeTwist.pointIdeal PS x) :
      ambientChartCoordinate (R := K) (σ := Fin 4) 0 i ∈ q.asIdeal := by
    exact (ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply PS xj _).mpr hi
  have hle : RingHom.ker (ambientPointKoszul_chartMap K) ≤ q.asIdeal := by
    rw [ambientPointKoszul_chartMap_ker, Ideal.span_le]
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc 1 h1
    · exact hc 2 h2
    · exact hc 3 h3
  have hm : (RingHom.ker (ambientPointKoszul_chartMap K)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (ambientPointKoszul_chartMap K)
      (ambientPointKoszul_chartMap_surjective K)
  have hq : q.asIdeal = RingHom.ker (ambientPointKoszul_chartMap K) :=
    (hm.eq_of_le q.isPrime.ne_top hle).symm
  let k : Spec (.of K) := default
  let yj : Proj.basicOpen PS (X (0 : Fin 4)) :=
    ⟨ambientPointKoszul_point K k, ambientPointKoszul_point_mem_basicOpen K k⟩
  have he : q = (ProjectiveSpectrum.Proj.toSpec PS (X (0 : Fin 4))).base yj :=
    PrimeSpectrum.ext (hq.trans (ambientPointKoszul_point_chartPrime K k).symm)
  let f := (ProjectiveSpectrum.Proj.toSpec PS (X (0 : Fin 4))).base
  letI : IsIso f := ProjectiveSpectrum.Proj.toSpec_base_isIso PS
    (isHomogeneous_X K 0) (by decide : 0 < 1)
  have hinj : Function.Injective f :=
    (TopCat.homeoOfIso (asIso f)).injective
  have hxy : xj = yj := hinj he
  exact ⟨k, (congrArg Subtype.val hxy).symm⟩

namespace ProjectiveNegativeTwist

set_option backward.isDefEq.respectTransparency false in
/-- Outside the actual standard point, at least one Koszul parameter is
a unit in every chosen standard-chart stalk coordinate. -/
theorem ambientPointKoszul_off_point_stalk_any_unit
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl)
    (hoff : x ∉ Set.range (ambientPointKoszul_point K)) :
    IsUnit (ambientPointKoszul_stalkParameter K 1 j x hx) ∨
      IsUnit (ambientPointKoszul_stalkParameter K 2 j x hx) ∨
      IsUnit (ambientPointKoszul_stalkParameter K 3 j x hx) := by
  have hc : X (1 : Fin 4) ∈ (pointIdeal PS x).primeCompl ∨
      X (2 : Fin 4) ∈ (pointIdeal PS x).primeCompl ∨
      X (3 : Fin 4) ∈ (pointIdeal PS x).primeCompl := by
    change X (1 : Fin 4) ∉ pointIdeal PS x ∨ X (2 : Fin 4) ∉ pointIdeal PS x ∨
      X (3 : Fin 4) ∉ pointIdeal PS x
    by_contra! hn
    exact hoff (ambientPointKoszul_mem_point_range_of_coordinates K x hn.1 hn.2.1 hn.2.2)
  rcases hc with h1 | h2 | h3
  · exact Or.inl ((localEquation_isUnit_iff PS (pointIdeal PS x)
      ⟨X 1, isHomogeneous_X K 1⟩ ⟨X j, isHomogeneous_X K j⟩ hx).mpr h1)
  · exact Or.inr (Or.inl ((localEquation_isUnit_iff PS (pointIdeal PS x)
      ⟨X 2, isHomogeneous_X K 2⟩ ⟨X j, isHomogeneous_X K j⟩ hx).mpr h2))
  · exact Or.inr (Or.inr ((localEquation_isUnit_iff PS (pointIdeal PS x)
      ⟨X 3, isHomogeneous_X K 3⟩ ⟨X j, isHomogeneous_X K j⟩ hx).mpr h3))

set_option backward.isDefEq.respectTransparency false in
/-- The actual final Koszul sheaf stalk map is surjective away from the point. -/
theorem ambientPointKoszul_last_stalk_surjective_off_range
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl)
    (hoff : x ∉ Set.range (ambientPointKoszul_point K)) :
    Function.Surjective ((schemeModuleStalkFunctor (Proj PS) x).map
      (pointGlobalTraceP3CoordinateKoszulLast K)) := by
  have hs := (ambientPointKoszul_exact_of_any_unit
    (ambientPointKoszul_stalkParameter K 1 j x hx)
    (ambientPointKoszul_stalkParameter K 2 j x hx)
    (ambientPointKoszul_stalkParameter K 3 j x hx)
    (ambientPointKoszul_off_point_stalk_any_unit K j x hx hoff)).2.2.2
  let e := ambientPointKoszul_stalkTripleCoordinate K j x hx 1
  let u := ambientPointKoszul_unitStalkCoordinate K x
  let d := threeGeneratorLast (ambientPointKoszul_stalkParameter K 1 j x hx)
    (ambientPointKoszul_stalkParameter K 2 j x hx) (ambientPointKoszul_stalkParameter K 3 j x hx)
  intro z
  obtain ⟨v, hv⟩ := hs (u z)
  refine ⟨e.symm v, u.injective ?_⟩
  calc
    _ = d (e (e.symm v)) := ambientPointKoszul_last_unit_stalk_coordinates K j x hx _
    _ = d v := congrArg d (e.apply_symm_apply v)
    _ = u z := hv

set_option backward.isDefEq.respectTransparency false in
/-- The actual augmented last Koszul pair is exact at every stalk outside
the standard point, with no augmentation-kernel comparison premise. -/
theorem ambientPointKoszul_last_augmentation_stalk_exact_off_range
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl)
    (hoff : x ∉ Set.range (ambientPointKoszul_point K)) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateKoszulLast K))
      ((schemeModuleStalkFunctor (Proj PS) x).map (ambientPointKoszul_augmentation K)) := by
  letI := ambientPointKoszul_pointModule_stalk_subsingleton_off_range K x hoff
  intro z
  constructor
  · intro _
    exact ambientPointKoszul_last_stalk_surjective_off_range K j x hx hoff z
  · intro _
    exact Subsingleton.elim _ _

end ProjectiveNegativeTwist
end PfaffianDescent
