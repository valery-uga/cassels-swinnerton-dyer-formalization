import AllCharacteristics.FiniteSubschemeRank
import AllCharacteristics.ProperFamilyGenericPointSpecialization

/-!
# Specializing a universal family of finite subschemes

Voisin moves a finite subscheme to the generic point of a smooth parameter
space, constructs a residual finite subscheme there, and specializes the
result back to the original field.  This file isolates the part of that
argument that begins once a universally closed parameter scheme with a
universal finite-flat family is available.

No representability theorem for a Hilbert functor is asserted here.  The
parameter scheme and its universal datum are explicit hypotheses.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AllCharacteristics

universe u

/-- Pull a universal finite-subscheme datum over a parameter scheme back to
a field-valued parameter. -/
noncomputable def finiteSubschemeParameterFiber
    {K : Type u} [Field K] {X H : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (h : H ⟶ Spec (.of K)) (n : ℕ)
    (D : FiniteSubschemeDatum (pullback.snd f h) n)
    (c : Spec (.of K) ⟶ H) :
    FiniteSubschemeDatum (pullback.snd (pullback.snd f h) c) n :=
  FiniteSubschemeDatum.baseChange
    (pullback.fst (pullback.snd f h) c) c
    (IsPullback.of_hasPullback (pullback.snd f h) c) D

/-- A field-valued parameter lying over the ground field determines an
actual finite subscheme of the original ambient scheme. -/
noncomputable def finiteSubschemeParameterFiniteSubschemeAt
    {K : Type u} [Field K] {X H : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (h : H ⟶ Spec (.of K)) (n : ℕ)
    (D : FiniteSubschemeDatum (pullback.snd f h) n)
    (c : Spec (.of K) ⟶ H) (hc : c ≫ h = 𝟙 _) :
    FiniteSubschemeDatum f n := by
  let g := pullback.snd f h
  let Dc := finiteSubschemeParameterFiber f h n D c
  let e := pullbackLeftPullbackSndIso f h c
  let m := pullback.fst f (c ≫ h)
  let i := Dc.val.subschemeι ≫ e.hom ≫ m
  haveI : IsIso m := by
    dsimp [m]
    rw [hc]
    infer_instance
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  have hem : e.hom ≫ m = pullback.fst g c ≫ pullback.fst f h := by
    dsimp [e, m, g]
    exact pullbackLeftPullbackSndIso_hom_fst f h c
  have hbase : i ≫ f = Dc.val.subschemeι ≫ pullback.snd g c := by
    calc
      i ≫ f = Dc.val.subschemeι ≫ (e.hom ≫ m) ≫ f := by
        simp only [i, Category.assoc]
      _ = Dc.val.subschemeι ≫ (pullback.fst g c ≫ pullback.fst f h) ≫ f := by
        rw [hem]
      _ = Dc.val.subschemeι ≫ pullback.fst g c ≫
          (pullback.fst f h ≫ f) := by rw [Category.assoc]
      _ = Dc.val.subschemeι ≫ pullback.fst g c ≫ (g ≫ h) := by
        rw [pullback.condition]
      _ = Dc.val.subschemeι ≫ (pullback.fst g c ≫ g) ≫ h := by
        rw [Category.assoc]
      _ = Dc.val.subschemeι ≫ (pullback.snd g c ≫ c) ≫ h := by
        rw [pullback.condition]
      _ = (Dc.val.subschemeι ≫ pullback.snd g c) ≫ (c ≫ h) := by
        rw [Category.assoc, Category.assoc]
      _ = Dc.val.subschemeι ≫ pullback.snd g c := by
        rw [hc, Category.comp_id]
  haveI : IsFinite (i ≫ f) := by
    rw [hbase]
    exact Dc.property.1
  haveI : Flat (i ≫ f) := by
    rw [hbase]
    exact Dc.property.2.1
  haveI : LocallyOfFinitePresentation (i ≫ f) := by
    rw [hbase]
    exact Dc.property.2.2.1
  exact finiteSubschemeDatumOfClosedImmersion i f n (fun s ↦ by
    have hs : s = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst s
    simpa only [hbase] using Dc.property.2.2.2 (IsLocalRing.closedPoint K))

/-- The effective cycle underlying the specialized finite subscheme has the
rank prescribed by the universal family. -/
theorem finiteSubschemeParameterFiniteSubschemeAt_cycle_degree
    {K : Type u} [Field K] {X H : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (h : H ⟶ Spec (.of K)) (n : ℕ)
    (D : FiniteSubschemeDatum (pullback.snd f h) n)
    (c : Spec (.of K) ⟶ H) (hc : c ≫ h = 𝟙 _) :
    EffectiveZeroCycle.degree f
      (finiteSubschemeDatumCycle f
        (finiteSubschemeParameterFiniteSubschemeAt f h n D c hc)) = n :=
  finiteSubschemeDatumCycle_degree f
    (finiteSubschemeParameterFiniteSubschemeAt f h n D c hc)

/-- Suppose a universally closed parameter space carries a universal
rank-`n` finite-flat subscheme of `X`.  A point of that parameter space over
the function field of a regular integral movement base specializes to an
effective degree-`n` zero-cycle on `X` over the ground field.

This is the scheme-theoretic specialization step in Voisin's generic Hilbert
scheme argument. -/
theorem exists_effectiveCycle_of_parameter_functionField_point
    {K : Type u} [Field K]
    {X H B : Scheme.{u}} [IsIntegral B]
    (f : X ⟶ Spec (.of K))
    (h : H ⟶ Spec (.of K)) [UniversallyClosed h] [LocallyOfFiniteType h]
    (n : ℕ) (D : FiniteSubschemeDatum (pullback.snd f h) n)
    (b : B ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ B) (hc : c ≫ b = 𝟙 _)
    [IsRegularLocalRing
      (B.presheaf.stalk (c (IsLocalRing.closedPoint K)))]
    (s : Spec B.functionField ⟶ H)
    (hs : s ≫ h = B.fromSpecStalk (genericPoint B) ≫ b) :
    ∃ z : EffectiveZeroCycle X, EffectiveZeroCycle.degree f z = n := by
  obtain ⟨q, hq⟩ :=
    universallyClosed_point_of_parameter_functionField_point b h c hc s hs
  exact
    ⟨finiteSubschemeDatumCycle f
        (finiteSubschemeParameterFiniteSubschemeAt f h n D q hq),
      finiteSubschemeParameterFiniteSubschemeAt_cycle_degree f h n D q hq⟩

/-- A packaged geometric input for specializing a generic finite subscheme.
It records exactly the parameter space, universal family, regular movement
base, and compatible function-field point used by the preceding theorem. -/
structure FiniteSubschemeGenericSpecializationData
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (n : ℕ) where
  H : Scheme.{u}
  B : Scheme.{u}
  h : H ⟶ Spec (.of K)
  universallyClosed_h : UniversallyClosed h
  locallyOfFiniteType_h : LocallyOfFiniteType h
  isIntegral_B : IsIntegral B
  universalDatum : FiniteSubschemeDatum (pullback.snd f h) n
  b : B ⟶ Spec (.of K)
  c : Spec (.of K) ⟶ B
  c_over : c ≫ b = 𝟙 _
  regular_c : IsRegularLocalRing
    (B.presheaf.stalk (c (IsLocalRing.closedPoint K)))
  genericPointMap : Spec B.functionField ⟶ H
  genericPointMap_over : genericPointMap ≫ h =
    B.fromSpecStalk (genericPoint B) ≫ b

/-- Packaged generic finite-subscheme specialization produces an effective
cycle of the stated degree over the ground field. -/
theorem FiniteSubschemeGenericSpecializationData.exists_effectiveCycle
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {n : ℕ}
    (data : FiniteSubschemeGenericSpecializationData f n) :
    ∃ z : EffectiveZeroCycle X, EffectiveZeroCycle.degree f z = n := by
  letI : UniversallyClosed data.h := data.universallyClosed_h
  letI : LocallyOfFiniteType data.h := data.locallyOfFiniteType_h
  letI : IsIntegral data.B := data.isIntegral_B
  letI : IsRegularLocalRing
      (data.B.presheaf.stalk (data.c (IsLocalRing.closedPoint K))) :=
    data.regular_c
  exact exists_effectiveCycle_of_parameter_functionField_point
    f data.h n data.universalDatum data.b data.c data.c_over
      data.genericPointMap data.genericPointMap_over

end AllCharacteristics
