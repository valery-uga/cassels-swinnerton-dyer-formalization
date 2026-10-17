import PfaffianDescent.ProjectiveClosedImmersion
import AllCharacteristics.CoordinateCharts
import AllCharacteristics.GradedChartCoordinates

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [CommRing K] {σ τ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (homogeneousSubmodule σ K))
    (J : HomogeneousIdeal (homogeneousSubmodule τ K))
    (g : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (hI : I.toIdeal ≤ J.toIdeal.comap g.toRingHom)

/-- A polynomial substitution respecting the equations descends to the
actual homogeneous coordinate rings. -/
noncomputable def polynomialQuotientMap : CoordinateRing I →+* CoordinateRing J :=
  Ideal.quotientMap J.toIdeal g.toRingHom hI

lemma polynomialQuotientMap_mk (p : MvPolynomial σ K) :
    polynomialQuotientMap I J g hI (Ideal.Quotient.mk I.toIdeal p) =
      Ideal.Quotient.mk J.toIdeal (g p) := Ideal.quotientMap_mk

lemma polynomialQuotientMap_base (a : K) :
    polynomialQuotientMap I J g hI (algebraMap K (CoordinateRing I) a) =
      algebraMap K (CoordinateRing J) a := by
  change polynomialQuotientMap I J g hI (Ideal.Quotient.mk I.toIdeal (C a)) =
    Ideal.Quotient.mk J.toIdeal (C a)
  rw [polynomialQuotientMap_mk]
  exact congrArg (Ideal.Quotient.mk J.toIdeal) (g.commutes a)

variable (hdeg : ∀ (n : ℕ) (p : MvPolynomial σ K), p.IsHomogeneous n → (g p).IsHomogeneous n)

noncomputable def polynomialQuotientGradingMap : grading I →+*ᵍ grading J where
  __ := polynomialQuotientMap I J g hI
  map_mem := by
    intro n x hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨g p, hdeg n p hp, (polynomialQuotientMap_mk I J g hI p).symm⟩

/-- The induced graded map has the expected action on a homogeneous
polynomial representative. -/
lemma polynomialQuotientGradingMap_mk (p : MvPolynomial σ K) :
    polynomialQuotientGradingMap I J g hI hdeg (Ideal.Quotient.mk I.toIdeal p) =
      Ideal.Quotient.mk J.toIdeal (g p) :=
  polynomialQuotientMap_mk I J g hI p

lemma polynomialQuotientGradingMap_surjective (hg : Function.Surjective g) :
    Function.Surjective (polynomialQuotientGradingMap I J g hI hdeg) :=
  Ideal.quotientMap_surjective (H := hI) hg

variable (hg : Function.Surjective g)

/-- A surjective homogeneous polynomial substitution gives an actual closed
projective embedding of the schemes defined by the equations. -/
noncomputable def polynomialProjectiveMap : scheme J ⟶ scheme I :=
  Proj.map (polynomialQuotientGradingMap I J g hI hdeg)
    (gradedSurjective_irrelevant_le _ (polynomialQuotientGradingMap_surjective I J g hI hdeg hg))

instance polynomialProjectiveMap_isClosedImmersion :
    IsClosedImmersion (polynomialProjectiveMap I J g hI hdeg hg) :=
  projectiveMap_closedImmersion_of_surjective _
    (polynomialQuotientGradingMap_surjective I J g hI hdeg hg)

/-- On the chart where a homogeneous target coordinate is nonzero, the
projective map induced by polynomial substitution is the localized
substitution map. -/
theorem awayι_polynomialProjectiveMap
    (s : CoordinateRing I) {d : ℕ}
    (hs : s ∈ grading I d) (hd : 0 < d) :
    Proj.awayι (grading J) (polynomialQuotientGradingMap I J g hI hdeg s)
        ((polynomialQuotientGradingMap I J g hI hdeg).map_mem hs) hd ≫
      polynomialProjectiveMap I J g hI hdeg hg =
    Spec.map (CommRingCat.ofHom
      (Away.map (polynomialQuotientGradingMap I J g hI hdeg) s)) ≫
        Proj.awayι (grading I) s hs hd := by
  exact Proj.awayι_comp_map
    (polynomialQuotientGradingMap I J g hI hdeg)
    (gradedSurjective_irrelevant_le _
      (polynomialQuotientGradingMap_surjective I J g hI hdeg hg)) hd s hs

/-- The affine substitution map preserves normalized homogeneous coordinate
ratios on the corresponding projective charts. -/
theorem awayMap_polynomialProjectiveMap_normalized
    (s t : CoordinateRing I)
    (hs : s ∈ grading I 1) (ht : t ∈ grading I 1) :
    Away.map (polynomialQuotientGradingMap I J g hI hdeg) s
      (AllCharacteristics.GradedChart.normalized (grading I) hs t ht) =
    AllCharacteristics.GradedChart.normalized (grading J)
      ((polynomialQuotientGradingMap I J g hI hdeg).map_mem hs)
      (polynomialQuotientGradingMap I J g hI hdeg t)
      ((polynomialQuotientGradingMap I J g hI hdeg).map_mem ht) := by
  unfold AllCharacteristics.GradedChart.normalized
  rw [Away.map_mk]

lemma polynomialQuotientGradingMap_away_base (s : CoordinateRing I) :
    (Away.map (polynomialQuotientGradingMap I J g hI hdeg) s).comp
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := s)) =
    AllCharacteristics.GradedChart.baseMap (grading J)
      (z := polynomialQuotientGradingMap I J g hI hdeg s) := by
  apply RingHom.ext
  intro a
  apply val_injective
  change Localization.mk (polynomialQuotientMap I J g hI (algebraMap K (CoordinateRing I) a))
    ⟨polynomialQuotientMap I J g hI 1, _⟩ = Localization.mk (algebraMap K (CoordinateRing J) a) 1
  rw [polynomialQuotientMap_base]
  exact congrArg (Localization.mk (algebraMap K (CoordinateRing J) a))
    (Subtype.ext (map_one (polynomialQuotientMap I J g hI)))

/-- Any homogeneous affine chart respects the coefficient structure map. -/
lemma homogeneousChart_toBase (s : CoordinateRing I) {d : ℕ}
    (hs : s ∈ grading I d) (hd : 0 < d) :
    Proj.awayι (grading I) s hs hd ≫ toBase I =
      Spec.map (CommRingCat.ofHom (AllCharacteristics.GradedChart.baseMap (grading I) (z := s))) := by
  change Proj.awayι (grading I) s hs hd ≫ (Proj.toSpecZero (grading I) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The actual projective embedding induced by polynomial substitution is a
morphism over the coefficient spectrum. -/
theorem polynomialProjectiveMap_toBase :
    polynomialProjectiveMap I J g hI hdeg hg ≫ toBase I = toBase J := by
  let F := polynomialQuotientGradingMap I J g hI hdeg
  let hF := gradedSurjective_irrelevant_le F
    (polynomialQuotientGradingMap_surjective I J g hI hdeg hg)
  let bI : Proj (grading I) ⟶ Spec (.of K) := toBase I
  let bJ : Proj (grading J) ⟶ Spec (.of K) := toBase J
  change Proj.map F hF ≫ bI = bJ
  apply (Proj.mapAffineOpenCover F hF).openCover.hom_ext
  intro s
  change (Σ d : PNat, grading I d) at s
  obtain ⟨⟨d, hd⟩, s, hs⟩ := s
  change s ∈ grading I d at hs
  change Proj.awayι (grading J) (F s) (F.2 hs) hd ≫
    (Proj.map F hF ≫ bI) =
    Proj.awayι (grading J) (F s) (F.2 hs) hd ≫ bJ
  have hbI : Proj.awayι (grading I) s hs hd ≫ bI =
      Spec.map (CommRingCat.ofHom (AllCharacteristics.GradedChart.baseMap (grading I) (z := s))) :=
    homogeneousChart_toBase I s hs hd
  have hbJ : Proj.awayι (grading J) (F s) (F.2 hs) hd ≫ bJ =
      Spec.map (CommRingCat.ofHom (AllCharacteristics.GradedChart.baseMap (grading J) (z := F s))) :=
    homogeneousChart_toBase J (F s) (F.2 hs) hd
  rw [← Category.assoc, Proj.awayι_comp_map F hF hd s hs, Category.assoc, hbI, hbJ, ← Spec.map_comp]
  apply congrArg Spec.map
  change CommRingCat.ofHom ((Away.map F s).comp
    (AllCharacteristics.GradedChart.baseMap (grading I))) =
    CommRingCat.ofHom (AllCharacteristics.GradedChart.baseMap (grading J))
  rw [polynomialQuotientGradingMap_away_base]

end
end PfaffianDescent
