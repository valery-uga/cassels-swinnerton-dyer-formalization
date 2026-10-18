import AllCharacteristics.FunctionFieldRationalMapDominance
import AllCharacteristics.ProjectivePoints

/-!
# Algebraic criteria for dominance of function-field constructions

The coordinate secant construction must do more than produce a nonzero cubic
solution: it must inject the coordinate ring of a nonempty target chart into
the source function field.  This file turns that algebraic fact into dominance
of an actual scheme rational map.  It also shows that the generic-image test
can be checked after any field extension, including a quadratic splitting
extension used by a conjugate-tangent construction.

No secant nonvanishing or algebraic-independence claim is asserted here.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-- A morphism between irreducible schemes is dominant exactly when it maps
the source generic point to the target generic point. -/
theorem Scheme.Hom.isDominant_iff_genericPoint_eq
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) :
    IsDominant f ↔ f (genericPoint X) = genericPoint Y := by
  constructor
  · intro hf
    letI : IsDominant f := hf
    have hgen : IsGenericPoint (f (genericPoint X)) (Set.univ : Set Y) := by
      simpa only [Set.image_univ, f.denseRange.closure_range] using
        (genericPoint_spec X).image f.continuous
    exact hgen.eq (genericPoint_spec Y)
  · exact f.isDominant_of_genericPoint_eq

/-- The morphism of affine schemes induced by an injective ring map is
dominant.  This direction does not require reducedness of the source ring. -/
theorem Scheme.isDominant_specMap_of_injective
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : Function.Injective g) :
    IsDominant (Spec.map (CommRingCat.ofHom g)) := by
  rw [isDominant_iff]
  change DenseRange (PrimeSpectrum.comap g)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot g).mp hg]
  exact bot_le

/-- Over a reduced affine target, dominance of a map on spectra is exactly
injectivity of the coefficient map. -/
theorem Scheme.isDominant_specMap_iff_injective
    {A B : Type u} [CommRing A] [_root_.IsReduced A] [CommRing B]
    (g : A →+* B) :
    IsDominant (Spec.map (CommRingCat.ofHom g)) ↔ Function.Injective g := by
  rw [isDominant_iff]
  change DenseRange (PrimeSpectrum.comap g) ↔ Function.Injective g
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (nilradical_eq_bot_iff).mpr (inferInstance : _root_.IsReduced A),
    le_bot_iff, RingHom.injective_iff_ker_eq_bot]

/-- Whether a field-valued point is generic is unchanged by extending its
coefficient field.  The assertion concerns actual scheme morphisms. -/
theorem Scheme.Hom.fieldPoint_generic_iff_after_extension
    {K L : Type u} [Field K] [Field L] {Y : Scheme.{u}}
    [IrreducibleSpace Y] (q : Spec (.of K) ⟶ Y) (φ : K →+* L) :
    (Spec.map (CommRingCat.ofHom φ) ≫ q)
        (genericPoint (Spec (.of L))) = genericPoint Y ↔
      q (genericPoint (Spec (.of K))) = genericPoint Y := by
  have hφ : Spec.map (CommRingCat.ofHom φ)
      (genericPoint (Spec (.of L))) = genericPoint (Spec (.of K)) :=
    Subsingleton.elim _ _
  rw [Scheme.Hom.comp_apply, hφ]

/-- Dominance of a field-valued point can be checked after an arbitrary field
extension; in particular the extension need not be finite or separable. -/
theorem Scheme.Hom.fieldPoint_isDominant_iff_after_extension
    {K L : Type u} [Field K] [Field L] {Y : Scheme.{u}}
    [IrreducibleSpace Y] (q : Spec (.of K) ⟶ Y) (φ : K →+* L) :
    IsDominant (Spec.map (CommRingCat.ofHom φ) ≫ q) ↔ IsDominant q := by
  rw [Scheme.Hom.isDominant_iff_genericPoint_eq,
    Scheme.Hom.isDominant_iff_genericPoint_eq]
  exact q.fieldPoint_generic_iff_after_extension φ

end AlgebraicGeometry

namespace AllCharacteristics

universe u

/-- A function-field point whose coefficient extension is dominant spreads
out to a dominant rational map over the original ground field. -/
theorem dominant_rationalMap_of_functionField_map_after_field_extension
    {k L : Type u} [Field k] [Field L] {X Y : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (ybase : Y ⟶ Spec (.of k)) [LocallyOfFiniteType ybase]
    [IrreducibleSpace Y]
    (q : Spec X.functionField ⟶ Y)
    (hq : q ≫ ybase = X.fromSpecStalk _ ≫ xbase)
    (φ : X.functionField →+* L)
    (hdominant : IsDominant (Spec.map (CommRingCat.ofHom φ) ≫ q)) :
    ∃ f : X ⤏ Y, f.IsDominant ∧
      f.compHom ybase = xbase.toRationalMap := by
  have hqdominant : IsDominant q :=
    (q.fieldPoint_isDominant_iff_after_extension φ).mp hdominant
  exact dominant_rationalMap_of_functionField_map xbase ybase q hq
    ((Scheme.Hom.isDominant_iff_genericPoint_eq q).mp hqdominant)

namespace HomogeneousProjective

variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An injective homomorphism from a standard projective chart to a field
defines a dominant field-valued point of the actual projective scheme. -/
theorem isDominant_projective_point_of_injective_chart_hom
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    [IrreducibleSpace (scheme I)] {K : Type u} [Field K]
    (j : σ) (g : ChartRing I j →+* K) (hg : Function.Injective g) :
    IsDominant (Spec.map (CommRingCat.ofHom g) ≫ chartι I j) := by
  letI : Nonempty (Spec (.of (ChartRing I j))) :=
    ⟨Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint K)⟩
  letI : IsDominant (Spec.map (CommRingCat.ofHom g)) :=
    Scheme.isDominant_specMap_of_injective g hg
  letI : IsDominant (chartι I j) :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace (chartι I j)
      (chartι I j).isOpenEmbedding.isOpenMap⟩
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- Injecting an actual target chart ring into the source function field
produces a dominant rational map over the base field.  The source remains the
specified integral scheme rather than an abstract field spectrum. -/
theorem dominant_rationalMap_of_injective_projective_chart_hom
    {k : Type u} [Field k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X] [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    [IrreducibleSpace (scheme I)]
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (j : σ) (g : ChartRing I j →+* X.functionField)
    (hgbase : g.comp (chartBaseMap I j) = φ.hom)
    (hg : Function.Injective g) :
    ∃ f : X ⤏ scheme I, f.IsDominant ∧
      f.compHom (toBase I) = xbase.toRationalMap := by
  let q : Spec X.functionField ⟶ scheme I :=
    Spec.map (CommRingCat.ofHom g) ≫ chartι I j
  have hq : q ≫ toBase I = X.fromSpecStalk _ ≫ xbase := by
    dsimp only [q]
    rw [Category.assoc, chartι_toBase, ← Spec.map_comp]
    calc
      Spec.map (CommRingCat.ofHom (chartBaseMap I j) ≫ CommRingCat.ofHom g) =
          Spec.map φ := by
            congr 1
            exact CommRingCat.hom_ext hgbase
      _ = X.fromSpecStalk _ ≫ xbase := hφ
  have hqdominant : IsDominant q :=
    isDominant_projective_point_of_injective_chart_hom I j g hg
  exact dominant_rationalMap_of_functionField_map xbase (toBase I) q hq
    ((Scheme.Hom.isDominant_iff_genericPoint_eq q).mp hqdominant)

end HomogeneousProjective
end AllCharacteristics
