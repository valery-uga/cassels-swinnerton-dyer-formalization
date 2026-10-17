import PfaffianDescent.CorayGenericNormalizationAffineDefectLinearExact

/-! Primitive original p/q caller for the SAME normalization LES on the
genuinely chosen actual affine defect. Original projection image is retained.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Package the actual normalization affine LES at an ABSTRACT integral
scheme. The only geometric inputs are closed Q-support and a genuine affine
neighbourhood containing the point and that support; exactness is DERIVED
from the accepted original map theorem, never a package premise. -/
private theorem nativeNormalizationAffineDefectExists002
    {K : Type u} [Field K] [CharZero K]
    (X : Scheme.{u}) [IsIntegral X] (pi : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType pi] (x : X)
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (haffine : ∃ U : X.affineOpens, Nonempty U.1 ∧
      schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U.1 ∧ x ∈ U.1) :
    letI : LocallyOfFiniteType pi := inferInstance
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    ∃ (U : X.affineOpens) (hnonempty : Nonempty U.1)
      (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
      (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U.1),
      letI : Nonempty U.1 := hnonempty
      let σ := genericNormalizationAffineDefectProjectionLinearMap X pi hclosed U.1 U.2 hsU
      let δ := genericNormalizationAffineDefectConnectingLinearMap X pi hclosed U.1 U.2 hsU
      let g := genericNormalizationCohomologyOneToNormalizationLinearMap X pi
      x ∈ U.1 ∧ Function.Exact σ δ ∧ Function.Exact δ g ∧
        δ.ker = LinearMap.range σ ∧ g.ker = LinearMap.range δ ∧ Function.Surjective g := by
  letI : LocallyOfFiniteType pi := inferInstance
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  obtain ⟨U, hnonempty, hsU, hxU⟩ := haffine
  letI : Nonempty U.1 := hnonempty
  exact ⟨U, hnonempty, hclosed, hsU, hxU,
    genericNormalizationAffineDefect_lowDegree_exact_surjective_and_kernels
      X pi hclosed U.1 U.2 hsU⟩

/-- The EXISTING original polynomial geometry constructs the same support-
containing nonempty affine neighbourhood, independently of LES packaging. -/
private def originalProjectiveNormalizationAffineCover002

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :=
  projectiveIntersection_genericNormalizationQuotient_exists_affineOpen
    p q hp hp0 n hq hnot x

/-- The EXISTING original geometry proves closedness, independently of
existential map/cohomology packing. No new support hypothesis is introduced. -/
private def originalProjectiveNormalizationClosedSupport002

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :=
  projectiveIntersection_genericNormalizationQuotient_stalkSupport_isClosed
    p q hp hp0 n hq hnot

/-- Curried SAME abstract normalization producer. Integral/LFT dictionaries
are explicit factory arguments, preventing trailing-instance synthesis while
capturing partial actual applications. No exactness outcome is a premise. -/
private def nativeNormalizationAffineDefectCurried003
    {K : Type u} [Field K] [CharZero K]
    (X : Scheme.{u}) (hX : IsIntegral X) :=
  fun (pi : X ⟶ Spec (CommRingCat.of K)) (hpi : LocallyOfFiniteType pi) =>
    @nativeNormalizationAffineDefectExists002 K (inferInstance : Field K)
      (inferInstance : CharZero K) X hX pi hpi

/-- Capture ONLY an abstract Scheme. The ORIGINAL integral dictionary
remains an EXPLICIT later argument, separated from scheme substitution. -/
private def nativeNormalizationAffineDefectSchemeOnly005
    {K : Type u} [Field K] [CharZero K] (X : Scheme.{u}) :=
  fun (hX : IsIntegral X) => nativeNormalizationAffineDefectCurried003 (K := K) X hX

/-- SAME original projective scheme as a named VALUE; primitive equation
parameters only. No integral/smooth/support/exactness data assumed. -/
private def originalNormalizationProjectiveSchemeValue005
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n) : Scheme.{u} :=
  scheme (projectiveIntersectionIdeal p q hp hq)

/-- Ordinary native Scheme value identity, no kernel debugging API. -/
private theorem originalNormalizationProjectiveSchemeValue_eq005
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n) :
    originalNormalizationProjectiveSchemeValue005 p q hp n hq = scheme (projectiveIntersectionIdeal p q hp hq) := rfl

/-- Independently capture EXACT original incoming integral dictionary.
No support/affine/normalization outcome is supplied. -/
private theorem originalNormalizationProjectiveIntegralRaw005

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :
    IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)) := inferInstance

/-- The SAME original integral proof on the named native Scheme value;
only the just-defined SAME scheme carrier is exposed at this boundary. -/
private theorem originalNormalizationProjectiveIntegralNamed005

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :
    IsIntegral (originalNormalizationProjectiveSchemeValue005 p q hp n hq) :=
  originalNormalizationProjectiveIntegralRaw005 p q hp hp0 n hq hnot x

/-- SAME original projective structure morphism on SAME named carrier. -/
private def originalNormalizationProjectiveBaseMapValue005
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n) :
    originalNormalizationProjectiveSchemeValue005 p q hp n hq ⟶ Spec (CommRingCat.of K) :=
  toBase (projectiveIntersectionIdeal p q hp hq)

/-- Original projective map supplies LFT on the exact named native arrow. -/
private theorem originalNormalizationProjectiveBaseMapFiniteType005
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n) :
    LocallyOfFiniteType (originalNormalizationProjectiveBaseMapValue005 p q hp n hq) := by
  change LocallyOfFiniteType (toBase (projectiveIntersectionIdeal p q hp hq))
  infer_instance

/-- SAME original selected x, typed on SAME named Scheme carrier. -/
private def originalNormalizationProjectivePointValue005

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :
    originalNormalizationProjectiveSchemeValue005 p q hp n hq := x

/-- Bounded ORIGINAL scheme/dictionary boundary005: supply ONLY named SAME original Scheme, before integral proof. No extra actual geometry or LES outcome input. -/
private def originalNormalizationActualSchemeOnlyFactory005

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :=
  nativeNormalizationAffineDefectSchemeOnly005 (K := K)
    (originalNormalizationProjectiveSchemeValue005 p q hp n hq)

/-- Bounded ORIGINAL scheme/dictionary boundary005: supply ONLY independently captured SAME integral dictionary. No extra actual geometry or LES outcome input. -/
private def originalNormalizationActualIntegralFactory005

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :=
  originalNormalizationActualSchemeOnlyFactory005 p q hp hp0 n hq hnot x
    (originalNormalizationProjectiveIntegralNamed005 p q hp hp0 n hq hnot x)

/-- Bounded ORIGINAL scheme/dictionary boundary005: supply ONLY independently typed SAME original π. No extra actual geometry or LES outcome input. -/
private def originalNormalizationActualBaseMapFactory005

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :=
  originalNormalizationActualIntegralFactory005 p q hp hp0 n hq hnot x
    (originalNormalizationProjectiveBaseMapValue005 p q hp n hq)

/-- Bounded ORIGINAL scheme/dictionary boundary005: supply ONLY independently derived SAME π LFT witness. No extra actual geometry or LES outcome input. -/
private def originalNormalizationActualFiniteTypeFactory005

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :=
  originalNormalizationActualBaseMapFactory005 p q hp hp0 n hq hnot x
    (originalNormalizationProjectiveBaseMapFiniteType005 p q hp n hq)

/-- Bounded ORIGINAL scheme/dictionary boundary005: supply ONLY independently typed SAME original point x. No extra actual geometry or LES outcome input. -/
private def originalNormalizationActualPointFactory005

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :=
  originalNormalizationActualFiniteTypeFactory005 p q hp hp0 n hq hnot x
    (originalNormalizationProjectivePointValue005 p q hp hp0 n hq hnot x)

/-- Bounded ORIGINAL scheme/dictionary boundary005: supply ONLY proved original closed normalization quotient support. No extra actual geometry or LES outcome input. -/
private def originalNormalizationActualClosedSupportFactory005

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :=
  originalNormalizationActualPointFactory005 p q hp hp0 n hq hnot x
    (originalProjectiveNormalizationClosedSupport002 p q hp hp0 n hq hnot x)

/-- Bounded ORIGINAL scheme/dictionary boundary005: supply ONLY constructed original affine neighbourhood, infer SAME actual LES existential. No extra actual geometry or LES outcome input. -/
private def originalNormalizationActualAffineExactNative005

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :=
  originalNormalizationActualClosedSupportFactory005 p q hp hp0 n hq hnot x
    (originalProjectiveNormalizationAffineCover002 p q hp hp0 n hq hnot x)

/-- Specialize the proved abstract existential producer ONCE, with precisely
the original X/pi and the previously constructed two geometric facts. -/
private def originalProjectiveNormalizationAffineExactProof002

    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :=
  originalNormalizationActualAffineExactNative005 p q hp hp0 n hq hnot x

/-- EXACT ORIGINAL public proposition as a value, independently of any
proof conversion. Its parameters, leading native dictionaries, σ/δ/g and
all kernel/range/surjectivity conclusions are copied verbatim from the
original public header. This declaration does not assert that proposition. -/
private def originalNormalizationExactPublicProposition006
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) : Prop :=
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let pi := toBase I
    letI : LocallyOfFiniteType pi := inferInstance
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    ∃ (U : X.affineOpens) (hnonempty : Nonempty U.1)
      (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
      (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U.1),
      letI : Nonempty U.1 := hnonempty
      let σ := genericNormalizationAffineDefectProjectionLinearMap X pi hclosed U.1 U.2 hsU
      let δ := genericNormalizationAffineDefectConnectingLinearMap X pi hclosed U.1 U.2 hsU
      let g := genericNormalizationCohomologyOneToNormalizationLinearMap X pi
      x ∈ U.1 ∧ Function.Exact σ δ ∧ Function.Exact δ g ∧
        δ.ker = LinearMap.range σ ∧ g.ker = LinearMap.range δ ∧ Function.Surjective g

/-- The already-derived ORIGINAL native producer, with ONLY the three
named original scheme/map/point aliases exposed syntactically in its type.
No geometric proof is redone and no exactness, support or affine outcome
is assumed. The public target is explicitly fixed by the separate value. -/
private theorem originalNormalizationExactPublicFromLiteralCarriers006
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :
    originalNormalizationExactPublicProposition006 p q hp hp0 n hq hnot x := by
  have h := originalProjectiveNormalizationAffineExactProof002
    p q hp hp0 n hq hnot x
  unfold originalNormalizationProjectiveSchemeValue005
    originalNormalizationProjectiveBaseMapValue005
    originalNormalizationProjectivePointValue005 at h
  exact h

/-- Literal original smooth-cubic/selected-intersection data construct one
actual nonempty affine open containing the chosen point AND all actual Q
support, then derive the actual linear LES with both projection/connecting
kernel contributions. No support, exactness, comparison or genus certificate. -/
theorem projectiveIntersection_genericNormalization_exists_affineDefect_lowDegreeLinearExact
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let pi := toBase I
    letI : LocallyOfFiniteType pi := inferInstance
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    ∃ (U : X.affineOpens) (hnonempty : Nonempty U.1)
      (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
      (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U.1),
      letI : Nonempty U.1 := hnonempty
      let σ := genericNormalizationAffineDefectProjectionLinearMap X pi hclosed U.1 U.2 hsU
      let δ := genericNormalizationAffineDefectConnectingLinearMap X pi hclosed U.1 U.2 hsU
      let g := genericNormalizationCohomologyOneToNormalizationLinearMap X pi
      x ∈ U.1 ∧ Function.Exact σ δ ∧ Function.Exact δ g ∧
        δ.ker = LinearMap.range σ ∧ g.ker = LinearMap.range δ ∧ Function.Surjective g :=
  originalNormalizationExactPublicFromLiteralCarriers006 p q hp hp0 n hq hnot x

end PfaffianDescent.Coray
end
