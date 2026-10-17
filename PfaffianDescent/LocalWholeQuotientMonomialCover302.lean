import PfaffianDescent.ActualAffineHilbertLocalCharts301
import Mathlib.AlgebraicGeometry.Cover.Open

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u v w

/-- Compose native affine open covers without replacing their affine objects. -/
def affineOpenCover_bind302 {X : Scheme.{u}} (U : X.AffineOpenCover.{v})
    (V : ∀ i, (Spec (U.X i)).AffineOpenCover.{w}) : X.AffineOpenCover.{max v w} where
  I₀ := Σ i : U.I₀, (V i).I₀
  X i := (V i.1).X i.2
  f i := (V i.1).f i.2 ≫ U.f i.1
  idx := Scheme.Cover.idx (U.openCover.bind (fun i => (V i).openCover))
  covers := Scheme.Cover.covers (U.openCover.bind (fun i => (V i).openCover))

/-- Indices contain actual localized quotient bases, not an assumed covering family. -/
def LocalWholeQuotientBasisIndex302 {A : Type u} [CommRing A] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) A)) (n : ℕ) :=
  Σ s : A, Basis (Fin n) (Localization.Away s)
    (MvPolynomial (Fin m) (Localization.Away s) ⧸
      I.map (MvPolynomial.map (algebraMap A (Localization.Away s))))

/-- Local basis existence outside each prime constructs a genuine affine open cover. -/
def localWholeQuotientBasisAffineCover302 {A : Type u} [CommRing A] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin m) A))
    (hb : ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal, Nonempty
      (Basis (Fin n) (Localization.Away s)
        (MvPolynomial (Fin m) (Localization.Away s) ⧸
          I.map (MvPolynomial.map (algebraMap A (Localization.Away s)))))) :
    (Spec (.of A)).AffineOpenCover where
  I₀ := LocalWholeQuotientBasisIndex302 I n
  X i := .of (Localization.Away i.1)
  f i := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away i.1)))
  idx p := ⟨(hb p).choose, Classical.choice (hb p).choose_spec.2⟩
  covers p := by
    have h := PrimeSpectrum.localization_away_comap_range
      (Localization.Away (hb p).choose) (hb p).choose
    exact (eq_iff_iff.mp congr(p ∈ $h)).mpr (hb p).choose_spec.1

/-- The explicit two-stage test-scheme cover: local bases, then actual monomial determinant opens. -/
def localWholeQuotientMonomialAffineCover302 {A : Type u} [CommRing A] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin m) A))
    (hb : ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal, Nonempty
      (Basis (Fin n) (Localization.Away s)
        (MvPolynomial (Fin m) (Localization.Away s) ⧸
          I.map (MvPolynomial.map (algebraMap A (Localization.Away s))))))
    (hn : 0 < n) : (Spec (.of A)).AffineOpenCover :=
  affineOpenCover_bind302 (localWholeQuotientBasisAffineCover302 I hb)
    (fun i => wholeQuotientMonomialBasisAffineCover299
      (I.map (MvPolynomial.map (algebraMap A (Localization.Away i.1)))) i.2 hn)

/-- The cover rings are the literal successive coefficient localizations. -/
lemma localWholeQuotientMonomialAffineCover_X302 {A : Type u} [CommRing A] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin m) A))
    (hb : ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal, Nonempty
      (Basis (Fin n) (Localization.Away s)
        (MvPolynomial (Fin m) (Localization.Away s) ⧸
          I.map (MvPolynomial.map (algebraMap A (Localization.Away s)))))) (hn : 0 < n)
    (i : LocalWholeQuotientBasisIndex302 I n) (q : MonomialBasisOpenIndex299 m n) :
    (localWholeQuotientMonomialAffineCover302 I hb hn).X ⟨i, q⟩ =
      CommRingCat.of (Localization.Away (wholeIdealMonomialTransitionDet290
        (I.map (MvPolynomial.map (algebraMap A (Localization.Away i.1)))) i.2 q.val.1)) := rfl

/-- The test-scheme patch maps are the actual two localization maps into the original base. -/
lemma localWholeQuotientMonomialAffineCover_f302 {A : Type u} [CommRing A] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin m) A))
    (hb : ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal, Nonempty
      (Basis (Fin n) (Localization.Away s)
        (MvPolynomial (Fin m) (Localization.Away s) ⧸
          I.map (MvPolynomial.map (algebraMap A (Localization.Away s)))))) (hn : 0 < n)
    (i : LocalWholeQuotientBasisIndex302 I n) (q : MonomialBasisOpenIndex299 m n) :
    (localWholeQuotientMonomialAffineCover302 I hb hn).f ⟨i, q⟩ =
      Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away i.1)
        (Localization.Away (wholeIdealMonomialTransitionDet290
          (I.map (MvPolynomial.map (algebraMap A (Localization.Away i.1)))) i.2 q.val.1)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away i.1))) := rfl

end PfaffianDescent
