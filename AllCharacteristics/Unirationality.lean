import AllCharacteristics.TwoProofs
import AllCharacteristics.UnirationalityCycle
import AllCharacteristics.FiniteFieldCubicPoint
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Birational.Dominant
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Unirational cubic surfaces

This file gives the standard rational-map definition of unirationality over a
field and formalizes the zero-cycle implication used in the final corollary
of `2-proofs.tex`.
-/

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AllCharacteristics
namespace HomogeneousProjective

universe u

/-- A scheme over `k` is unirational when a finite-dimensional affine space
has a dominant rational map to it over `Spec k`. -/
def IsUnirationalOver (k : Type u) [Field k]
    (X : Scheme.{u}) (x : X ⟶ Spec.{u} (CommRingCat.of.{u} k)) : Prop :=
  ∃ (n : ℕ) (f : AffineSpace.{u} (ULift.{u} (Fin n))
      (Spec.{u} (CommRingCat.of.{u} k)) ⤏ X),
    f.IsDominant ∧ f.compHom x =
      (AffineSpace.{u} (ULift.{u} (Fin n))
        (Spec.{u} (CommRingCat.of.{u} k)) ↘
          Spec.{u} (CommRingCat.of.{u} k)).toRationalMap

/-- A birational parametrization by a finite-dimensional affine space supplies
an `IsUnirationalOver` witness. -/
theorem isUnirationalOver_of_birationalOver_affineSpace
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (y : Y ⟶ Spec (.of k)) (n : ℕ)
    (h : Scheme.BirationalOver y
      (AffineSpace.{u} (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k))) :
    IsUnirationalOver k Y y := by
  let A := AffineSpace.{u} (ULift.{u} (Fin n)) (Spec (.of k))
  let a : A ⟶ Spec (.of k) := A ↘ Spec (.of k)
  letI : A.Over (Spec (.of k)) := ⟨a⟩
  letI : Y.Over (Spec (.of k)) := ⟨y⟩
  rcases h with ⟨e, he⟩
  let f : A.PartialIso Y := e.symm
  have hf : f.IsOver a y := by
    exact he.symm
  refine ⟨n, f.toRationalMap, ?_, ?_⟩
  · rw [f.toPartialMap.isDominant_toRationalMap_iff]
    change IsDominant (f.iso.hom ≫ f.target.ι)
    letI : IsDominant f.iso.hom := inferInstance
    letI : IsDominant f.target.ι := Opens.isDominant_ι f.dense_target
    infer_instance
  · letI : f.toPartialMap.IsOver (Spec (.of k)) := by
      constructor
      change f.iso.hom ≫ f.target.ι ≫ y = f.source.ι ≫ a
      exact hf
    exact Scheme.RationalMap.isOver_iff.mp
      (inferInstance : f.toRationalMap.IsOver (Spec (.of k)))

/-- The Segre--Manin--Kollár implication used by the paper: a smooth cubic
surface with a rational section is unirational. -/
def SmoothCubicPointUnirationalFor (k : Type u) [Field k] : Prop :=
  ∀ (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase F hF)]
    (s : Spec (.of k) ⟶ hypersurface F hF),
    s ≫ hypersurfaceToBase F hF = 𝟙 _ →
      IsUnirationalOver k (hypersurface F hF) (hypersurfaceToBase F hF)

/-- The point-to-cycle part of the unirationality argument: a rational map
from affine space which is defined at a ground-field point gives a
degree-one zero-cycle on its separated target. -/
theorem zeroCycle_degree_one_of_affine_partialMap_domain_section
    {k : Type u} [Field k] {n : ℕ}
    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of k)) [IsSeparated y]
    (f : (AffineSpace.{u} (ULift.{u} (Fin n))
      (Spec.{u} (CommRingCat.of.{u} k))).PartialMap Y)
    (hbase : f.hom ≫ y = f.domain.ι ≫
      (AffineSpace.{u} (ULift.{u} (Fin n))
        (Spec.{u} (CommRingCat.of.{u} k)) ↘
          Spec.{u} (CommRingCat.of.{u} k)))
    (q : Spec (.of k) ⟶ f.domain)
    (hq : q ≫ f.domain.ι ≫
      (AffineSpace.{u} (ULift.{u} (Fin n))
        (Spec.{u} (CommRingCat.of.{u} k)) ↘
          Spec.{u} (CommRingCat.of.{u} k)) = 𝟙 _) :
    ∃ z : ZeroCycle Y, ZeroCycle.degree y z = 1 :=
  zeroCycle_degree_one_of_partialMap_domain_section _ y f hbase q hq

/-- Over an infinite field, the zero-cycle implication in the
unirationality corollary follows from a rational map's dense affine domain. -/
theorem zeroCycle_degree_one_of_unirational_infinite
    {k : Type u} [Field k] [Infinite k]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of k)) [IsSeparated y]
    (hY : IsUnirationalOver k Y y) :
    ∃ z : ZeroCycle Y, ZeroCycle.degree y z = 1 := by
  obtain ⟨n, f, hfdominant, hfbase⟩ := hY
  letI : (AffineSpace (ULift.{u} (Fin n))
      (Spec (.of k))).Over (Spec (.of k)) :=
    ⟨AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)⟩
  letI : Y.Over (Spec (.of k)) := ⟨y⟩
  letI : f.IsOver (Spec (.of k)) :=
    Scheme.RationalMap.isOver_iff.mpr hfbase
  obtain ⟨g, hgOver, hgf⟩ :=
    Scheme.RationalMap.exists_partialMap_over (Spec (.of k)) f
  have hgbase : g.hom ≫ y = g.domain.ι ≫
      (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)) :=
    Scheme.PartialMap.isOver_iff.mp hgOver
  exact zeroCycle_degree_one_of_affine_partialMap_infinite y g hgbase

/-- For a smooth cubic surface, unirationality gives a degree-one zero-cycle
over every field.  Finite fields use Chevalley--Warning; infinite fields use
a rational point of the dense affine domain. -/
theorem zeroCycle_degree_one_of_unirational_smoothCubic
    {k : Type u} [Field k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase F hF)]
    (hY : IsUnirationalOver k (hypersurface F hF) (hypersurfaceToBase F hF)) :
    ∃ z : ZeroCycle (hypersurface F hF),
      ZeroCycle.degree (hypersurfaceToBase F hF) z = 1 := by
  classical
  rcases finite_or_infinite k with hfinite | hinfinite
  · letI : Finite k := hfinite
    obtain ⟨s, hs⟩ := finite_field_cubic_has_rational_section F hF
    exact twoProofs_zeroCycle_degree_one_of_section F hF s hs
  · letI : Infinite k := hinfinite
    letI : IsSeparated (hypersurfaceToBase F hF) :=
      @IsProper.toIsSeparated _ _ _ (isProper_hypersurfaceToBase F hF)
    exact zeroCycle_degree_one_of_unirational_infinite _ hY

/-- The paper's unirationality corollary over infinite fields.  Its forward
implication is proved from the affine rational-map domain, so no separate
index input is needed. -/
theorem twoProofs_unirational_iff_zeroCycle_degree_one_of_infinite
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K],
      VoisinDegreeTenEffectiveDegreeFourFor K)
    {k : Type u} [Field k] [Infinite k]
    (smk : SmoothCubicPointUnirationalFor k)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase F hF)] :
    IsUnirationalOver k (hypersurface F hF) (hypersurfaceToBase F hF) ↔
      ∃ z : ZeroCycle (hypersurface F hF),
        ZeroCycle.degree (hypersurfaceToBase F hF) z = 1 := by
  letI : IsSeparated (hypersurfaceToBase F hF) :=
    @IsProper.toIsSeparated _ _ _ (isProper_hypersurfaceToBase F hF)
  constructor
  · exact zeroCycle_degree_one_of_unirational_infinite _
  · intro hz
    obtain ⟨s, hs⟩ := (twoProofs_main_theorem_of_effectiveDegreeFour coray geometry F hF).mpr hz
    exact smk F hF s hs

/-- Corollary 1.3 of `2-proofs.tex`, with its Segre--Manin--Kollár input
spelled out and the paper's Coray--Voisin inputs retained explicitly. -/
theorem twoProofs_unirational_iff_zeroCycle_degree_one
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K],
      VoisinDegreeTenEffectiveDegreeFourFor K)
    {k : Type u} [Field k]
    (smk : SmoothCubicPointUnirationalFor k)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase F hF)] :
    IsUnirationalOver k (hypersurface F hF) (hypersurfaceToBase F hF) ↔
      ∃ z : ZeroCycle (hypersurface F hF),
        ZeroCycle.degree (hypersurfaceToBase F hF) z = 1 := by
  constructor
  · exact zeroCycle_degree_one_of_unirational_smoothCubic F hF
  · intro hz
    obtain ⟨s, hs⟩ := (twoProofs_main_theorem_of_effectiveDegreeFour coray geometry F hF).mpr hz
    exact smk F hF s hs

end HomogeneousProjective
end AllCharacteristics
