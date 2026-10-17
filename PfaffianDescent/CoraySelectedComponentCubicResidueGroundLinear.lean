import PfaffianDescent.CoraySelectedComponentCubicResidueTrace
import PfaffianDescent.CorayOwnCartierResidueGroundLinear
import PfaffianDescent.CubicIntrinsicCanonicalTraceGroundLinear

/-! Original-K linearity of the SAME selected-component residue trace.
No duality/perfectness/genus assertion. SOURCE ONLY / UNVERIFIED.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian MvPolynomial TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem nativeResidueTraceComposition_toAdd
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module K M] [Module K N]
    (tau : N ≃ₗ[K] K) (delta : M →ₗ[K] N)
    (tau0 : N ≃+ K) (delta0 : M →+ N)
    (htau : tau.toAddEquiv = tau0) (hdelta : delta.toAddMonoidHom = delta0) :
    (tau.toLinearMap.comp delta).toAddMonoidHom = tau0.toAddMonoidHom.comp delta0 := by
  change tau.toAddEquiv.toAddMonoidHom.comp delta.toAddMonoidHom = _
  rw [htau, hdelta]

/-- Scalar compatibility is assembled at ordinary module variables.
The original additive trace and original boundary function are retained. -/
private theorem nativeOriginalAdditiveComposition_smul003
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module K M] [Module K N]
    (tau : N →+ K) (delta : M →ₗ[K] N)
    (htau : ∀ (c : K) (z : N), tau (c • z) = c • tau z) :
    ∀ (c : K) (z : M),
      (tau.comp delta.toAddMonoidHom) (c • z) =
        c • (tau.comp delta.toAddMonoidHom) z := by
  intro c z
  exact (congrArg tau (delta.map_smul c z)).trans (htau c (delta z))

/-- The SAME original Laurent additive coefficient trace, constructed at p
alone before any selected component or its regular immersion is substituted. -/
private def originalCubicCoefficientAdditiveTrace005
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
    let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : HasExt.{u} X.Modules := ‹HasExt.{u} (hypersurface p hp).Modules›
    letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
    schemeModuleCohomology X W 2 →+ K := by
  let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
  let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
  letI : HasExt.{u} X.Modules := ‹HasExt.{u} (hypersurface p hp).Modules›
  letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
  letI : (equationIdeal p hp).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := inferInstance
  let intrinsicExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules :=
    ‹HasExt.{u} (hypersurface p hp).Modules›
  exact (@cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K
    (inferInstance : Field K) p hp hp0
    (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
    ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› intrinsicExt).toAddMonoidHom

/-- Normalize only the cubic coefficient scalar action; no selected
component, immersion, boundary or residue sequence enters this cut. -/
private theorem originalCubicCoefficientAdditiveTrace_smul005
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
    let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : HasExt.{u} X.Modules := ‹HasExt.{u} (hypersurface p hp).Modules›
    letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
    letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
    ∀ (c : K) (z : schemeModuleCohomology X W 2),
      (originalCubicCoefficientAdditiveTrace005 p hp hp0) (c • z) = c • (originalCubicCoefficientAdditiveTrace005 p hp hp0) z := by
  let intrinsicExt : HasExt.{u} (hypersurface p hp).Modules :=
    ‹HasExt.{u} (hypersurface p hp).Modules›
  let X : Scheme.{u} := Proj (grading (equationIdeal p hp))
  let W : X.Modules := sheafOfModules (grading (equationIdeal p hp)) 1
  letI : HasExt.{u} X.Modules := intrinsicExt
  letI : Linear K X.Modules := schemeModulesLinearOver (hypersurfaceToBase p hp)
  letI : AddCommGroup (schemeModuleCohomology X W 2) := Ext.instAddCommGroup
  letI : Module K (schemeModuleCohomology X W 2) := Ext.instModule
  letI : (equationIdeal p hp).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := inferInstance
  exact @cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv_smul K
    (inferInstance : Field K) p hp hp0
    (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
    ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› intrinsicExt

/-- Native Cartier residue scalar compatibility at ordinary Scheme and
immersion variables, before original selected-component geometry is inserted. -/
private theorem nativeActualCartierTrace_smul005
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W)
    (tau : schemeModuleCohomology X W 2 →+ K)
    (htau : letI : Linear K X.Modules := schemeModulesLinearOver pi
      ∀ (c : K) (z : schemeModuleCohomology X W 2),
        tau (c • z) = c • tau z) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ∀ (c : K) (z : schemeModuleCohomology X (H.actualCartierResidueSequence W).X₃ 1),
      (H.actualCartierResidueTrace W hW tau) (c • z) =
        c • (H.actualCartierResidueTrace W hW tau) z := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  change ∀ (c : K) (z : schemeModuleCohomology X (H.actualCartierResidueSequence W).X₃ 1),
    tau (H.actualCartierResidueBoundary W hW (c • z)) =
      c • tau (H.actualCartierResidueBoundary W hW z)
  exact nativeOriginalAdditiveComposition_smul003 tau
    (H.actualCartierResidueBoundaryLinearMap pi W hW) htau

/-- Transport scalar compatibility using a separately proved pointwise
application formula; no complete additive-map equality is compared. -/
private theorem nativeScalarTransportByApply005
    {M : Type u} [SMul K M] (f g : M → K)
    (hfg : ∀ z, f z = g z)
    (hg : ∀ (c : K) (z : M), g (c • z) = c • g z) :
    ∀ (c : K) (z : M), f (c • z) = c • f z := by
  intro c z
  exact (hfg (c • z)).trans
    ((hg c z).trans (congrArg (fun t : K => c • t) (hfg z).symm))

/-- Pointwise application of the ORIGINAL selected additive map is
exactly original coefficient trace after the actual Cartier boundary.
This cut contains no scalar action and no independently constructed LinearMap. -/
private theorem selectedOriginalResidueTrace_apply005
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    let hCp : p ∈ C.toIdeal := hCmin.le (by
      rw [projectiveIntersectionIdeal_toIdeal]
      exact Ideal.subset_span (Set.mem_insert p {q}))
    let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
    letI : IsClosedImmersion i :=
      PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
    let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
      p q hp hp0 n hq hnot C hCmin
    let W := sheafOfModules (grading (equationIdeal p hp)) 1
    ∀ z : schemeModuleCohomology (hypersurface p hp)
        (H.actualCartierResidueSequence W).X₃ 1,
      selectedProjectiveMinimalComponent_actualCubicResidueTrace p q hp hp0 n hq hnot C hCmin z =
        (originalCubicCoefficientAdditiveTrace005 p hp hp0) (H.actualCartierResidueBoundary W
          (cubicIntrinsicNegativeOne_locallyRankOne p hp) z) := by
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
  letI : IsClosedImmersion i :=
    PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin
  let W := sheafOfModules (grading (equationIdeal p hp)) 1
  change ∀ z : schemeModuleCohomology (hypersurface p hp)
      (H.actualCartierResidueSequence W).X₃ 1,
    selectedProjectiveMinimalComponent_actualCubicResidueTrace p q hp hp0 n hq hnot C hCmin z =
      (originalCubicCoefficientAdditiveTrace005 p hp hp0) (H.actualCartierResidueBoundary W
        (cubicIntrinsicNegativeOne_locallyRankOne p hp) z)
  intro z
  rfl

/-- Infer the generic Cartier scalar law at the SAME actual selected
regular immersion and the independently normalized original coefficient trace. -/
private def selectedActualCartierTraceScalar005
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :=
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
  letI : IsClosedImmersion i :=
    PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin
  let W := sheafOfModules (grading (equationIdeal p hp)) 1
  nativeActualCartierTrace_smul005 (X := hypersurface p hp)
    (hypersurfaceToBase p hp) H W
    (cubicIntrinsicNegativeOne_locallyRankOne p hp)
    (originalCubicCoefficientAdditiveTrace005 p hp hp0) (originalCubicCoefficientAdditiveTrace_smul005 p hp hp0)

/-- Construct the original selected-map scalar law from the separately
checked application formula and native actual Cartier scalar specialization. -/
private def selectedOriginalTraceScalarFromApply005
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :=
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
  letI : IsClosedImmersion i :=
    PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin
  let W := sheafOfModules (grading (equationIdeal p hp)) 1
  letI : Linear K (hypersurface p hp).Modules :=
    schemeModulesLinearOver (hypersurfaceToBase p hp)
  nativeScalarTransportByApply005
    (selectedProjectiveMinimalComponent_actualCubicResidueTrace p q hp hp0 n hq hnot C hCmin)
    (H.actualCartierResidueTrace W (cubicIntrinsicNegativeOne_locallyRankOne p hp) (originalCubicCoefficientAdditiveTrace005 p hp hp0))
    (selectedOriginalResidueTrace_apply005 p q hp hp0 n hq hnot C hCmin)
    (selectedActualCartierTraceScalar005 p q hp hp0 n hq hnot C hCmin)

private theorem selectedProjectiveMinimalComponent_actualCubicResidueTrace_smul003
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    let hCp : p ∈ C.toIdeal := hCmin.le (by
      rw [projectiveIntersectionIdeal_toIdeal]
      exact Ideal.subset_span (Set.mem_insert p {q}))
    let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
    letI : IsClosedImmersion i :=
      PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
    let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
      p q hp hp0 n hq hnot C hCmin
    let W := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : Linear K (hypersurface p hp).Modules :=
      schemeModulesLinearOver (hypersurfaceToBase p hp)
    ∀ (c : K) (z : schemeModuleCohomology (hypersurface p hp)
      (H.actualCartierResidueSequence W).X₃ 1),
      selectedProjectiveMinimalComponent_actualCubicResidueTrace
        p q hp hp0 n hq hnot C hCmin (c • z) =
      c • selectedProjectiveMinimalComponent_actualCubicResidueTrace
        p q hp hp0 n hq hnot C hCmin z := by
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
  letI : IsClosedImmersion i :=
    PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin
  let W := sheafOfModules (grading (equationIdeal p hp)) 1
  letI : Linear K (hypersurface p hp).Modules :=
    schemeModulesLinearOver (hypersurfaceToBase p hp)
  exact selectedOriginalTraceScalarFromApply005 p q hp hp0 n hq hnot C hCmin


def selectedProjectiveMinimalComponent_actualCubicResidueTraceLinearMap
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    let hCp : p ∈ C.toIdeal := hCmin.le (by
      rw [projectiveIntersectionIdeal_toIdeal]
      exact Ideal.subset_span (Set.mem_insert p {q}))
    let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
    letI : IsClosedImmersion i :=
      PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
    let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
      p q hp hp0 n hq hnot C hCmin
    let W := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : Linear K (hypersurface p hp).Modules :=
      schemeModulesLinearOver (hypersurfaceToBase p hp)
    schemeModuleCohomology (hypersurface p hp)
      (H.actualCartierResidueSequence W).X₃ 1 →ₗ[K] K := by
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
  letI : IsClosedImmersion i :=
    PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin
  let W := sheafOfModules (grading (equationIdeal p hp)) 1
  letI : Linear K (hypersurface p hp).Modules :=
    schemeModulesLinearOver (hypersurfaceToBase p hp)
  exact
    { toAddHom := (selectedProjectiveMinimalComponent_actualCubicResidueTrace
        p q hp hp0 n hq hnot C hCmin).toAddHom
      map_smul' := selectedProjectiveMinimalComponent_actualCubicResidueTrace_smul003
        p q hp hp0 n hq hnot C hCmin }


theorem selectedProjectiveMinimalComponent_actualCubicResidueTraceLinearMap_toAddMonoidHom
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    let hCp : p ∈ C.toIdeal := hCmin.le (by
      rw [projectiveIntersectionIdeal_toIdeal]
      exact Ideal.subset_span (Set.mem_insert p {q}))
    let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
    letI : IsClosedImmersion i :=
      PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
    let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
      p q hp hp0 n hq hnot C hCmin
    let W := sheafOfModules (grading (equationIdeal p hp)) 1
    letI : Linear K (hypersurface p hp).Modules :=
      schemeModulesLinearOver (hypersurfaceToBase p hp)
    (selectedProjectiveMinimalComponent_actualCubicResidueTraceLinearMap
      p q hp hp0 n hq hnot C hCmin).toAddMonoidHom =
      selectedProjectiveMinimalComponent_actualCubicResidueTrace
        p q hp hp0 n hq hnot C hCmin := by
  rfl

end PfaffianDescent.Coray
