import PfaffianDescent.CorayActualNormalizedCubicGenericNoTangency
import PfaffianDescent.CorayPlaneHyperplaneRestriction
import PfaffianDescent.CorayPlaneCubicSmoothFromFieldPoints
import AllCharacteristics.ProjectiveFiberSmoothness

/-! SOURCE ONLY / UNVERIFIED149. The ORIGINAL smooth cubic over ANY field
constructs an ACTUAL native smooth generic plane cubic. Generic coefficients,
original-chart no-tangency, polynomial restriction/chain rule, all residue-field
Jacobian covers and native Fin3 smoothness are constructed internally. Neither
smooth plane section, chosen coordinate-cut smoothness, genus/Hilbert bound,
Infinite original K nor constants=K is a supplied final-caller premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every actual normalized point of the SAME generic plane equation, over
any extension of its parameter field, has a nonzero partial. The original
smooth cubic internally excludes the contrary via its genuine no-tangency. -/
theorem genericPlaneCubic_normalizedFieldPoint_exists_nonzero_partial
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    [Algebra (GenericHyperplaneField K) M]
    [IsScalarTower K (GenericHyperplaneField K) M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (y : Fin 3 → M) (j : Fin 3) (hyj : y j = 1)
    (hpy : (genericPlaneCubic p).eval₂ (algebraMap (GenericHyperplaneField K) M) y = 0) :
    ∃ i : Fin 3, (MvPolynomial.pderiv i (genericPlaneCubic p)).eval₂
      (algebraMap (GenericHyperplaneField K) M) y ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let L := GenericHyperplaneField K
  let f := algebraMap L M
  let t : Fin 3 → L := genericHyperplaneCoefficient (K := K)
  let x : Fin 4 → M := planeHyperplanePointLift f t y
  have hxj : x j.succ = 1 := by simpa only [x, planeHyperplanePointLift, Fin.cases_succ] using hyj
  have hcoef : f.comp (algebraMap K L) = algebraMap K M :=
    (IsScalarTower.algebraMap_eq K L M).symm
  have hpx : MvPolynomial.aeval x p = 0 := by
    change (planeHyperplaneRestrictionHom t (p.map (algebraMap K L))).eval₂ f y = 0 at hpy
    rw [planeHyperplaneRestrictionHom_eval₂, MvPolynomial.eval₂_map, hcoef] at hpy
    exact hpy
  have hgradient : ∀ i : Fin 3,
      MvPolynomial.aeval x (MvPolynomial.pderiv i.succ p) =
        MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p) * f (t i) := by
    intro i
    have hi := h i
    change (MvPolynomial.pderiv i
      (planeHyperplaneRestrictionHom t (p.map (algebraMap K L)))).eval₂ f y = 0 at hi
    rw [planeHyperplaneRestrictionHom_pderiv_eval₂] at hi
    simp only [MvPolynomial.pderiv_map, MvPolynomial.eval₂_map, hcoef] at hi
    change MvPolynomial.aeval x (MvPolynomial.pderiv i.succ p) -
      f (t i) * MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p) = 0 at hi
    exact (sub_eq_zero.mp hi).trans (mul_comm _ _)
  apply smoothCubic_normalizedPoint_not_genericHyperplane_normal p hp hp0 x j.succ hxj hpx
  exact ⟨MvPolynomial.aeval x (MvPolynomial.pderiv (0 : Fin 4) p), rfl, hgradient⟩

/-- The actual restricted equation is nonzero. A zero equation would make
all partials vanish at the literal normalized point [1:0:0], contradicting
the internally derived pointwise nonsingularity. -/
theorem genericPlaneCubic_ne_zero
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] : genericPlaneCubic p ≠ 0 := by
  intro hz
  let y : Fin 3 → GenericHyperplaneField K := Pi.single 0 1
  have hy : y 0 = 1 := by simp [y]
  have hpy : (genericPlaneCubic p).eval₂
      (algebraMap (GenericHyperplaneField K) (GenericHyperplaneField K)) y = 0 := by simp [hz]
  obtain ⟨i, hi⟩ :=
    genericPlaneCubic_normalizedFieldPoint_exists_nonzero_partial p hp hp0 y 0 hy hpy
  simpa [hz] using hi

/-- The ORIGINAL smooth cubic internally constructs actual generic plane
chart partial unit ideals. No pointwise/partial-cover/smooth-plane certificate
is a caller input. -/
theorem smoothCubic_actualGenericPlaneCubic_chart_partial_span_top
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 3) :
    Ideal.span (Set.range (plane_chartPDeriv (genericPlaneCubic p)
      (genericPlaneCubic_isHomogeneous p hp) j)) = ⊤ := by
  apply planeCubic_chart_partial_span_top_of_fieldPoints _
    (genericPlaneCubic_isHomogeneous p hp) _ j
  intro M _ _ y a hya hpy
  let L := GenericHyperplaneField K
  letI : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun b => rfl
  exact genericPlaneCubic_normalizedFieldPoint_exists_nonzero_partial p hp hp0 y a hya hpy

/-- The SAME original smooth cubic produces native smoothness of its actual
generic plane section. The final caller supplies no pointwise/Jacobian/smooth
plane conclusion: every such construction input is generated in the proof. -/
theorem smoothCubic_actualGenericPlaneCubic_smooth
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    Smooth (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) := by
  exact plane_smooth_hypersurface_of_chart_pderiv_span _
    (genericPlaneCubic_isHomogeneous p hp)
    (smoothCubic_actualGenericPlaneCubic_chart_partial_span_top p hp hp0)

/-- The SAME actual plane section is native smooth of relative dimension
ONE, from its real three-variable/two-relation presentation. This is the
correct dimension input for subsequent regular curve/Cartier-divisor work. -/
theorem smoothCubic_actualGenericPlaneCubic_smoothOfRelativeDimension_one
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    SmoothOfRelativeDimension 1
      (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
  plane_smoothOfRelativeDimension_one_hypersurface_of_chart_pderiv_span _
    (genericPlaneCubic_isHomogeneous p hp)
    (smoothCubic_actualGenericPlaneCubic_chart_partial_span_top p hp hp0)

/-- Every further coefficient extension keeps the SAME actual generic
plane section smooth. This includes an algebraic closure of the parameter
field, with no change to the original curve's whole ideal. -/
theorem smoothCubic_actualGenericPlaneCubic_map_smooth
    {K M : Type u} [Field K] [Field M]
    (f : GenericHyperplaneField K →+* M)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    Smooth (hypersurfaceToBase ((genericPlaneCubic p).map f)
      ((genericPlaneCubic_isHomogeneous p hp).map f)) := by
  letI : Smooth (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_smooth p hp hp0
  exact smooth_hypersurfaceToBase_map f _ _

end PfaffianDescent.Coray
