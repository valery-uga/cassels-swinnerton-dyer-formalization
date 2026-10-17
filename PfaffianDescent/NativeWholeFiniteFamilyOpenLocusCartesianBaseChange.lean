import PfaffianDescent.NativeFiniteFamilyOpenLocus314
import PfaffianDescent.RelativeFiniteFlatHilbertFunctor197
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Whole finite-family good opens commute with arbitrary actual Cartesian
base change. The195 application constructs its original whole subscheme
comparison and source square internally, and197 derives its ambient square
from the actual slice morphism. No reducedness, source comparison, good-open
or cover outcome is supplied to either concrete caller. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false

/-- Actual scheme pullback image identity, applied to the entire bad closed set. -/
private theorem actualCartesian_badImage_complement_preimage001
    {Z0 Z B0 B : Scheme.{u}} (r : Z0 ⟶ Z) (f0 : Z0 ⟶ B0)
    (f : Z ⟶ B) (b : B0 ⟶ B) (H : IsPullback r f0 f b) (V : Z.Opens) :
    ((f0 '' (((r ⁻¹ᵁ V) : Set Z0)ᶜ))ᶜ) =
      b ⁻¹' ((f '' ((V : Set Z)ᶜ))ᶜ) := by
  change (f0.base '' (r.base ⁻¹' ((V : Set Z)ᶜ)))ᶜ =
    b.base ⁻¹' ((f.base '' ((V : Set Z)ᶜ))ᶜ)
  rw [Scheme.image_preimage_eq_of_isPullback H, Set.preimage_compl]

/-- Structural intermediate for entire native family diagrams. The concrete
195/197 callers below CONSTRUCT both this square and the actual embedding
comparison; no desired good-locus equality is a structural premise. -/
theorem finiteFamilyWholeOpenLocus_cartesian_eq_preimage001
    {X0 X B0 B : Scheme.{u}} (d : X0 ⟶ X) (F0 : X0 ⟶ B0)
    (F : X ⟶ B) (b : B0 ⟶ B) (n : ℕ)
    (P0 : FiniteFlatHilbertPoint195 F0 n) (P : FiniteFlatHilbertPoint195 F n)
    (r : P0.val.subscheme ⟶ P.val.subscheme)
    (hEmbedding : r ≫ P.val.subschemeι = P0.val.subschemeι ≫ d)
    (H : IsPullback r (P0.val.subschemeι ≫ F0) (P.val.subschemeι ≫ F) b)
    (U : X.Opens) :
    finiteFamilyWholeOpenLocus314 F0 n P0 (d ⁻¹ᵁ U) =
      b ⁻¹ᵁ finiteFamilyWholeOpenLocus314 F n P U := by
  have hOpen : P0.val.subschemeι ⁻¹ᵁ (d ⁻¹ᵁ U) =
      r ⁻¹ᵁ (P.val.subschemeι ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← hEmbedding, Scheme.Hom.comp_preimage]
  apply TopologicalSpace.Opens.ext
  change ((P0.val.subschemeι ≫ F0) ''
      (((P0.val.subschemeι ⁻¹ᵁ (d ⁻¹ᵁ U)) : Set P0.val.subscheme)ᶜ))ᶜ =
    b ⁻¹' (((P.val.subschemeι ≫ F) ''
      (((P.val.subschemeι ⁻¹ᵁ U) : Set P.val.subscheme)ᶜ))ᶜ)
  rw [hOpen]
  exact actualCartesian_badImage_complement_preimage001 r
    (P0.val.subschemeι ≫ F0) (P.val.subschemeι ≫ F) b H (P.val.subschemeι ⁻¹ᵁ U)

/-- Canonical comparison of the WHOLE195 pulled-back source, using comapIso. -/
private def actualWholeBaseChange195_sourceComparison001
    {X0 X B0 B : Scheme.{u}} (d : X0 ⟶ X) (F0 : X0 ⟶ B0)
    (F : X ⟶ B) (b : B0 ⟶ B) (H : IsPullback d F0 F b) (n : ℕ)
    (P : FiniteFlatHilbertPoint195 F n) :
    (finiteFlatHilbertBaseChange195 d F0 F b H n P).val.subscheme ⟶ P.val.subscheme :=
  (P.val.comapIso d).hom ≫ pullback.snd d P.val.subschemeι

/-- The canonical whole-source comparison retains the original ambient embedding. -/
private theorem actualWholeBaseChange195_sourceComparison_embedding001
    {X0 X B0 B : Scheme.{u}} (d : X0 ⟶ X) (F0 : X0 ⟶ B0)
    (F : X ⟶ B) (b : B0 ⟶ B) (H : IsPullback d F0 F b) (n : ℕ)
    (P : FiniteFlatHilbertPoint195 F n) :
    actualWholeBaseChange195_sourceComparison001 d F0 F b H n P ≫ P.val.subschemeι =
      (finiteFlatHilbertBaseChange195 d F0 F b H n P).val.subschemeι ≫ d := by
  change ((P.val.comapIso d).hom ≫ pullback.snd d P.val.subschemeι) ≫ P.val.subschemeι =
    (P.val.comap d).subschemeι ≫ d
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, P.val.comapIso_hom_fst d]

/-- Actual whole-source Cartesian square is DERIVED by pullback pasting and
the canonical comapIso; it is not assumed in the concrete basechange theorem. -/
private theorem actualWholeBaseChange195_sourceComparison_isPullback001
    {X0 X B0 B : Scheme.{u}} (d : X0 ⟶ X) (F0 : X0 ⟶ B0)
    (F : X ⟶ B) (b : B0 ⟶ B) (H : IsPullback d F0 F b) (n : ℕ)
    (P : FiniteFlatHilbertPoint195 F n) :
    IsPullback (actualWholeBaseChange195_sourceComparison001 d F0 F b H n P)
      ((finiteFlatHilbertBaseChange195 d F0 F b H n P).val.subschemeι ≫ F0)
      (P.val.subschemeι ≫ F) b := by
  change IsPullback ((P.val.comapIso d).hom ≫ pullback.snd d P.val.subschemeι)
    ((P.val.comap d).subschemeι ≫ F0) (P.val.subschemeι ≫ F) b
  have Houter : IsPullback (pullback.snd d P.val.subschemeι)
      (pullback.fst d P.val.subschemeι ≫ F0) (P.val.subschemeι ≫ F) b :=
    (IsPullback.of_hasPullback d P.val.subschemeι).flip.paste_vert H
  refine Houter.of_iso' (P.val.comapIso d) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using
      congrArg (fun f => f ≫ F0) (P.val.comapIso_hom_fst d)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- Literal195 finite-flat base change commutes with the maximal whole-family
open locus. All original source maps and nilpotents are retained. -/
theorem finiteFamilyWholeOpenLocus_baseChange195001
    {X0 X B0 B : Scheme.{u}} (d : X0 ⟶ X) (F0 : X0 ⟶ B0)
    (F : X ⟶ B) (b : B0 ⟶ B) (H : IsPullback d F0 F b) (n : ℕ)
    (P : FiniteFlatHilbertPoint195 F n) (U : X.Opens) :
    finiteFamilyWholeOpenLocus314 F0 n
        (finiteFlatHilbertBaseChange195 d F0 F b H n P) (d ⁻¹ᵁ U) =
      b ⁻¹ᵁ finiteFamilyWholeOpenLocus314 F n P U :=
  finiteFamilyWholeOpenLocus_cartesian_eq_preimage001 d F0 F b n
    (finiteFlatHilbertBaseChange195 d F0 F b H n P) P
    (actualWholeBaseChange195_sourceComparison001 d F0 F b H n P)
    (actualWholeBaseChange195_sourceComparison_embedding001 d F0 F b H n P)
    (actualWholeBaseChange195_sourceComparison_isPullback001 d F0 F b H n P) U

/-- The actual good open is all of the base exactly when the ENTIRE original
family source lies in the actual ambient open. No reduced support replaces it. -/
theorem finiteFamilyWholeOpenLocus_eq_top_iff_entireSource_in_open001
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ)
    (P : FiniteFlatHilbertPoint195 F n) (U : X.Opens) :
    finiteFamilyWholeOpenLocus314 F n P U = ⊤ ↔
      Set.range P.val.subschemeι ⊆ (U : Set X) := by
  rw [← top_le_iff, finiteFamilyWholeOpenLocus_maximal314 F n P U]
  constructor
  · intro h x hx
    obtain ⟨z, rfl⟩ := hx
    exact h z (by trivial)
  · intro h z _
    exact h ⟨z, rfl⟩

/-- ALL actual slice morphisms preserve the whole-open locus of the literal197
point functor. Both ambient and whole-source Cartesian squares are constructed. -/
theorem relativeFiniteFlatHilbertWholeOpenLocus_baseChange001
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ) (U : X.Opens)
    {T0 T1 : Over B} (h : T0 ⟶ T1)
    (P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T1) n) :
    finiteFamilyWholeOpenLocus314 (relativeHilbertFamily197 F T0) n
        ((relativeFiniteFlatHilbertFunctor197 F n).map h.op P)
        (pullback.snd T0.hom F ⁻¹ᵁ U) =
      h.left ⁻¹ᵁ finiteFamilyWholeOpenLocus314 (relativeHilbertFamily197 F T1) n P
        (pullback.snd T1.hom F ⁻¹ᵁ U) := by
  have hOpen : pullback.snd T0.hom F ⁻¹ᵁ U =
      relativeHilbertAmbientMap197 F h ⁻¹ᵁ (pullback.snd T1.hom F ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, relativeHilbertAmbientMap_snd197]
  rw [hOpen, relativeFiniteFlatHilbertFunctor197_map_eq_baseChange195]
  exact finiteFamilyWholeOpenLocus_baseChange195001
    (relativeHilbertAmbientMap197 F h) (relativeHilbertFamily197 F T0)
    (relativeHilbertFamily197 F T1) h.left (relativeHilbertAmbientMap_isPullback197 F h) n P
    (pullback.snd T1.hom F ⁻¹ᵁ U)

end PfaffianDescent
end
