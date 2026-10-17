import PfaffianDescent.AmbientPointKoszulBasisPointPrime
import PfaffianDescent.PointGlobalTraceP3BasisUnitStalk
import PfaffianDescent.LocalExtResidueInjective

/-! # Actual augmentation and Koszul stalks away from the invertible-basis point -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
variable (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)

local instance ambientPointKoszul_basisOffPointPrime (x : Proj PS) :
    (ProjectiveNegativeTwist.pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

set_option backward.isDefEq.respectTransparency false in
/-- The actual pushed-forward point structure module has zero stalk
outside the image of the actual standard-point closed immersion. -/
theorem ambientPointKoszul_basisPointModule_stalk_subsingleton_off_range
    (x : Proj PS) (hx : x ∉ Set.range (ambientPointKoszul_basisPoint M hM)) :
    Subsingleton ((schemeModuleStalkFunctor (Proj PS) x).obj (ambientPointKoszul_basisPointModule M hM)) :=
  schemeModulePushforward_stalk_subsingleton_off_range
    (ambientPointKoszul_basisPoint M hM) (SheafOfModules.unit (Spec (.of K)).ringCatSheaf) x hx

set_option backward.isDefEq.respectTransparency false in
/-- The three coordinate equations vanish only on the actual invertible-basis point. -/
theorem ambientPointKoszul_mem_basisPoint_range_of_coordinates
    (x : Proj PS)
    (h1 : (ambientPointKoszul_basis M 1).val ∈ ProjectiveNegativeTwist.pointIdeal PS x)
    (h2 : (ambientPointKoszul_basis M 2).val ∈ ProjectiveNegativeTwist.pointIdeal PS x)
    (h3 : (ambientPointKoszul_basis M 3).val ∈ ProjectiveNegativeTwist.pointIdeal PS x) :
    x ∈ Set.range (ambientPointKoszul_basisPoint M hM) := by
  have hx0 : (ambientPointKoszul_basis M 0).val ∈ (ProjectiveNegativeTwist.pointIdeal PS x).primeCompl := by
    change (ambientPointKoszul_basis M 0).val ∉ ProjectiveNegativeTwist.pointIdeal PS x
    intro h0
    apply x.not_irrelevant_le
    apply (ambientPointKoszul_basis_span_irrelevant M hM).trans
    rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  let xj : Proj.basicOpen PS ((ambientPointKoszul_basis M 0).val) := ⟨x, hx0⟩
  let q := (ProjectiveSpectrum.Proj.toSpec PS ((ambientPointKoszul_basis M 0).val)).base xj
  have hc (i : Fin 4) (hi : (ambientPointKoszul_basis M i).val ∈ ProjectiveNegativeTwist.pointIdeal PS x) :
      ambientPointKoszul_basisChartCoordinate M 0 i ∈ q.asIdeal := by
    exact (ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply PS xj _).mpr hi
  have hle : RingHom.ker (ambientPointKoszul_basisChartMap M hM) ≤ q.asIdeal := by
    rw [ambientPointKoszul_basisChartMap_ker, Ideal.span_le]
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc 1 h1
    · exact hc 2 h2
    · exact hc 3 h3
  have hm : (RingHom.ker (ambientPointKoszul_basisChartMap M hM)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (ambientPointKoszul_basisChartMap M hM)
      (ambientPointKoszul_basisChartMap_surjective M hM)
  have hq : q.asIdeal = RingHom.ker (ambientPointKoszul_basisChartMap M hM) :=
    (hm.eq_of_le q.isPrime.ne_top hle).symm
  let k : Spec (.of K) := default
  let yj : Proj.basicOpen PS ((ambientPointKoszul_basis M 0).val) :=
    ⟨ambientPointKoszul_basisPoint M hM k, ambientPointKoszul_basisPoint_mem_basicOpen M hM k⟩
  have he : q = (ProjectiveSpectrum.Proj.toSpec PS ((ambientPointKoszul_basis M 0).val)).base yj :=
    PrimeSpectrum.ext (hq.trans (ambientPointKoszul_basisPoint_chartPrime M hM k).symm)
  let f := (ProjectiveSpectrum.Proj.toSpec PS ((ambientPointKoszul_basis M 0).val)).base
  letI : IsIso f := ProjectiveSpectrum.Proj.toSpec_base_isIso PS
    (ambientPointKoszul_basis M 0).property (by decide : 0 < 1)
  have hinj : Function.Injective f :=
    (TopCat.homeoOfIso (asIso f)).injective
  have hxy : xj = yj := hinj he
  exact ⟨k, (congrArg Subtype.val hxy).symm⟩

namespace ProjectiveNegativeTwist

set_option backward.isDefEq.respectTransparency false in
/-- Outside the actual invertible-basis point, at least one Koszul parameter is
a unit in every chosen standard-chart stalk coordinate. -/
theorem ambientPointKoszul_off_basisPoint_stalk_any_unit
    (j : Fin 4) (x : Proj PS) (hx : (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl)
    (hoff : x ∉ Set.range (ambientPointKoszul_basisPoint M hM)) :
    IsUnit (ambientPointKoszul_basisStalkParameter M 1 j x hx) ∨
      IsUnit (ambientPointKoszul_basisStalkParameter M 2 j x hx) ∨
      IsUnit (ambientPointKoszul_basisStalkParameter M 3 j x hx) := by
  have hc : (ambientPointKoszul_basis M 1).val ∈ (pointIdeal PS x).primeCompl ∨
      (ambientPointKoszul_basis M 2).val ∈ (pointIdeal PS x).primeCompl ∨
      (ambientPointKoszul_basis M 3).val ∈ (pointIdeal PS x).primeCompl := by
    change (ambientPointKoszul_basis M 1).val ∉ pointIdeal PS x ∨ (ambientPointKoszul_basis M 2).val ∉ pointIdeal PS x ∨
      (ambientPointKoszul_basis M 3).val ∉ pointIdeal PS x
    by_contra! hn
    exact hoff (ambientPointKoszul_mem_basisPoint_range_of_coordinates M hM x hn.1 hn.2.1 hn.2.2)
  rcases hc with h1 | h2 | h3
  · exact Or.inl ((localEquation_isUnit_iff PS (pointIdeal PS x)
      (ambientPointKoszul_basis M 1) (ambientPointKoszul_basis M j) hx).mpr h1)
  · exact Or.inr (Or.inl ((localEquation_isUnit_iff PS (pointIdeal PS x)
      (ambientPointKoszul_basis M 2) (ambientPointKoszul_basis M j) hx).mpr h2))
  · exact Or.inr (Or.inr ((localEquation_isUnit_iff PS (pointIdeal PS x)
      (ambientPointKoszul_basis M 3) (ambientPointKoszul_basis M j) hx).mpr h3))

set_option backward.isDefEq.respectTransparency false in
/-- The actual final Koszul sheaf stalk map is surjective away from the point. -/
theorem ambientPointKoszul_basisLast_stalk_surjective_off_range
    (j : Fin 4) (x : Proj PS) (hx : (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl)
    (hoff : x ∉ Set.range (ambientPointKoszul_basisPoint M hM)) :
    Function.Surjective ((schemeModuleStalkFunctor (Proj PS) x).map
      (pointGlobalTraceP3BasisKoszulLast K (ambientPointKoszul_basis M))) := by
  have hs := (ambientPointKoszul_exact_of_any_unit
    (ambientPointKoszul_basisStalkParameter M 1 j x hx)
    (ambientPointKoszul_basisStalkParameter M 2 j x hx)
    (ambientPointKoszul_basisStalkParameter M 3 j x hx)
    (ambientPointKoszul_off_basisPoint_stalk_any_unit M hM j x hx hoff)).2.2.2
  let e := pointGlobalTraceP3Basis_stalkTripleCoordinate K (ambientPointKoszul_basis M) j x hx 1
  let u := ambientPointKoszul_unitStalkCoordinate K x
  let d := threeGeneratorLast (ambientPointKoszul_basisStalkParameter M 1 j x hx)
    (ambientPointKoszul_basisStalkParameter M 2 j x hx) (ambientPointKoszul_basisStalkParameter M 3 j x hx)
  intro z
  obtain ⟨v, hv⟩ := hs (u z)
  refine ⟨e.symm v, u.injective ?_⟩
  calc
    _ = d (e (e.symm v)) := pointGlobalTraceP3Basis_last_unit_stalk_coordinates K (ambientPointKoszul_basis M) j x hx _
    _ = d v := congrArg d (e.apply_symm_apply v)
    _ = u z := hv

set_option backward.isDefEq.respectTransparency false in
/-- The actual augmented last Koszul pair is exact at every stalk outside
the invertible-basis point, with no augmentation-kernel comparison premise. -/
theorem ambientPointKoszul_basisLast_augmentation_stalk_exact_off_range
    (j : Fin 4) (x : Proj PS) (hx : (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl)
    (hoff : x ∉ Set.range (ambientPointKoszul_basisPoint M hM)) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisKoszulLast K (ambientPointKoszul_basis M)))
      ((schemeModuleStalkFunctor (Proj PS) x).map (ambientPointKoszul_basisAugmentation M hM)) := by
  letI := ambientPointKoszul_basisPointModule_stalk_subsingleton_off_range M hM x hoff
  intro z
  constructor
  · intro _
    exact ambientPointKoszul_basisLast_stalk_surjective_off_range M hM j x hx hoff z
  · intro _
    exact Subsingleton.elim _ _

end ProjectiveNegativeTwist
end PfaffianDescent
