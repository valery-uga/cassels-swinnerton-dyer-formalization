import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! SOURCE ONLY195. Literal degree-n finite-flat closed-subscheme test points.
Ideal sheaf data classifies whole embedded subschemes; no support replacement.
This is the point/base-change layer, not Hilbert representability. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- A literal finite-flat degree-n Hilbert test point in an actual family. -/
def FiniteFlatHilbertPoint195 {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ) : Type u :=
  { I : X.IdealSheafData //
    IsFinite (I.subschemeι ≫ F) ∧ Flat (I.subschemeι ≫ F) ∧
      ∀ y : B, (I.subschemeι ≫ F).finrank y = n }

/-- A supplied whole closed immersion determines its actual ideal-sheaf point.
The source-to-image isomorphism preserves its original base map and degree. -/
def closedImmersionHilbertPoint195
    {Z X B : Scheme.{u}} (F : X ⟶ B) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsFinite (i ≫ F)] [Flat (i ≫ F)]
    (n : ℕ) (hn : ∀ y : B, (i ≫ F).finrank y = n) :
    FiniteFlatHilbertPoint195 F n := by
  let e : Z ≅ i.ker.subscheme := asIso i.toImage
  have hfac : e.hom ≫ i.ker.subschemeι = i := by
    change i.toImage ≫ i.imageι = i
    exact i.toImage_imageι
  have hbase : i.ker.subschemeι ≫ F = e.inv ≫ (i ≫ F) := by
    calc
      _ = e.inv ≫ (e.hom ≫ i.ker.subschemeι) ≫ F := by simp
      _ = _ := by rw [hfac]
  have hfinite : IsFinite (i.ker.subschemeι ≫ F) := by
    rw [hbase]
    infer_instance
  have hflat : Flat (i.ker.subschemeι ≫ F) := by
    rw [hbase]
    infer_instance
  letI := hfinite
  letI := hflat
  refine ⟨i.ker, hfinite, hflat, ?_⟩
  intro y
  rw [hbase]
  exact (congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.inv (i ≫ F)) y).trans (hn y)

lemma closedImmersionHilbertPoint195_ideal
    {Z X B : Scheme.{u}} (F : X ⟶ B) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsFinite (i ≫ F)] [Flat (i ≫ F)]
    (n : ℕ) (hn : ∀ y : B, (i ≫ F).finrank y = n) :
    (closedImmersionHilbertPoint195 F i n hn).val = i.ker := rfl

/-- A genuine Cartesian square identifies the WHOLE pulled-back ideal,
including nilpotents, with the supplied original immersion's ideal. -/
lemma wholeIdeal_comap_eq_of_isPullback195
    {Z0 Z X0 X : Scheme.{u}}
    (r : Z0 ⟶ Z) (i : Z0 ⟶ X0) (i' : Z ⟶ X) (d : X0 ⟶ X)
    [IsClosedImmersion i'] (H : IsPullback r i i' d) :
    i'.ker.comap d = i.ker := by
  calc
    i'.ker.comap d = (pullback.fst d i').ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i' d).symm
    _ = (H.flip.isoPullback.hom ≫ pullback.fst d i').ker :=
      (Scheme.Hom.ker_comp_of_isIso H.flip.isoPullback.hom (pullback.fst d i')).symm
    _ = i.ker := congrArg (fun f : Z0 ⟶ X0 => f.ker) H.flip.isoPullback_hom_fst

/-- Literal Cartesian base change of a finite-flat Hilbert test point.
Finiteness, flatness, and degree are derived from the constructed pullback. -/
def finiteFlatHilbertBaseChange195
    {X0 X B0 B : Scheme.{u}}
    (d : X0 ⟶ X) (F0 : X0 ⟶ B0) (F : X ⟶ B) (b : B0 ⟶ B)
    (H : IsPullback d F0 F b) (n : ℕ) (I : FiniteFlatHilbertPoint195 F n) :
    FiniteFlatHilbertPoint195 F0 n := by
  let J := I.val.comap d
  let e := I.val.comapIso d
  let r := e.hom ≫ pullback.snd d I.val.subschemeι
  have Houter : IsPullback (pullback.snd d I.val.subschemeι)
      (pullback.fst d I.val.subschemeι ≫ F0) (I.val.subschemeι ≫ F) b :=
    (IsPullback.of_hasPullback d I.val.subschemeι).flip.paste_vert H
  have Hsame : IsPullback r (J.subschemeι ≫ F0) (I.val.subschemeι ≫ F) b := by
    refine Houter.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [r, Iso.refl_hom, Category.comp_id]
    · simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using
        congrArg (fun f => f ≫ F0) (I.val.comapIso_hom_fst d)
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  letI : IsFinite (I.val.subschemeι ≫ F) := I.property.1
  letI : Flat (I.val.subschemeι ≫ F) := I.property.2.1
  have hfinite : IsFinite (J.subschemeι ≫ F0) :=
    MorphismProperty.of_isPullback Hsame (inferInstance : IsFinite (I.val.subschemeι ≫ F))
  have hflat : Flat (J.subschemeι ≫ F0) :=
    MorphismProperty.of_isPullback Hsame (inferInstance : Flat (I.val.subschemeι ≫ F))
  letI := hfinite
  letI := hflat
  refine ⟨J, hfinite, hflat, ?_⟩
  intro y
  exact (Scheme.Hom.finrank_of_isPullback r (J.subschemeι ≫ F0)
    (I.val.subschemeι ≫ F) b Hsame y).trans (I.property.2.2 (b y))

lemma finiteFlatHilbertBaseChange195_ideal
    {X0 X B0 B : Scheme.{u}}
    (d : X0 ⟶ X) (F0 : X0 ⟶ B0) (F : X ⟶ B) (b : B0 ⟶ B)
    (H : IsPullback d F0 F b) (n : ℕ) (I : FiniteFlatHilbertPoint195 F n) :
    (finiteFlatHilbertBaseChange195 d F0 F b H n I).val = I.val.comap d := rfl

/-- Exact reduction of the literal point associated to a supplied immersion. -/
lemma finiteFlatHilbertBaseChange195_closedImmersion_ideal
    {Z0 Z X0 X B0 B : Scheme.{u}}
    (d : X0 ⟶ X) (F0 : X0 ⟶ B0) (F : X ⟶ B) (b : B0 ⟶ B)
    (H : IsPullback d F0 F b) (n : ℕ)
    (r : Z0 ⟶ Z) (i : Z0 ⟶ X0) (i' : Z ⟶ X)
    [IsClosedImmersion i'] [IsFinite (i' ≫ F)] [Flat (i' ≫ F)]
    (hn : ∀ y : B, (i' ≫ F).finrank y = n)
    (HZ : IsPullback r i i' d) :
    (finiteFlatHilbertBaseChange195 d F0 F b H n
      (closedImmersionHilbertPoint195 F i' n hn)).val = i.ker :=
  wholeIdeal_comap_eq_of_isPullback195 r i i' d HZ

end PfaffianDescent
