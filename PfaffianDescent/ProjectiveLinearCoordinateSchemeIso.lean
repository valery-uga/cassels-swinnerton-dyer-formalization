import PfaffianDescent.ProjectiveLinearCoordinateRank
import PfaffianDescent.GradedSurjection
import PfaffianDescent.PolynomialProjectiveMap
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Scheme isomorphisms from linear projective coordinate changes

An invertible linear change of homogeneous coordinates that carries one
homogeneous ideal to another induces an isomorphism of their actual Proj
schemes.  This upgrades the existing Hilbert-function transport to a
scheme-level statement.
-/

namespace PfaffianDescent

open MvPolynomial AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K]

/-- The graded coordinate-ring map induced by an invertible linear change of
coordinates. -/
noncomputable def linearCoordinateChangeGradedHom
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom) :
    grading I →+*ᵍ grading J where
  __ := (Ideal.quotientEquivAlg I.toIdeal J.toIdeal
    (linearSubstitutionEquiv M hM) hIJ).toRingEquiv.toRingHom
  map_mem := by
    intro n x hx
    obtain ⟨p, hp, hpx⟩ := hx
    rw [← hpx]
    change Ideal.quotientEquivAlg I.toIdeal J.toIdeal
      (linearSubstitutionEquiv M hM) hIJ (Ideal.Quotient.mk I.toIdeal p) ∈ grading J n
    have hIJ' : J.toIdeal = I.toIdeal.map
        (↑(linearSubstitutionEquiv M hM) : MvPolynomial (Fin 4) K →+*
          MvPolynomial (Fin 4) K) := by
      simpa using hIJ
    change Ideal.quotientEquivAlg I.toIdeal J.toIdeal
      (linearSubstitutionEquiv M hM) hIJ' (Ideal.Quotient.mk I.toIdeal p) ∈ grading J n
    rw [Ideal.quotientEquivAlg_mk]
    exact ⟨linearSubstitution M p, linearSubstitution_homogeneous M hp, rfl⟩

/-- The inverse change transports the homogeneous ideal back to its source. -/
theorem linearCoordinateChange_ideal_symm
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom) :
    I.toIdeal = J.toIdeal.map
      (↑(linearSubstitutionEquiv M hM).symm : MvPolynomial (Fin 4) K →+*
        MvPolynomial (Fin 4) K) := by
  rw [hIJ]
  exact (Ideal.map_of_equiv (linearSubstitutionEquiv M hM).toRingEquiv).symm

/-- The inverse graded coordinate-ring map. -/
noncomputable def linearCoordinateChangeGradedHomSymm
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom) :
    grading J →+*ᵍ grading I where
  __ := (Ideal.quotientEquivAlg J.toIdeal I.toIdeal
    (linearSubstitutionEquiv M hM).symm
    (linearCoordinateChange_ideal_symm M hM I J hIJ)).toRingEquiv.toRingHom
  map_mem := by
    intro n x hx
    obtain ⟨p, hp, hpx⟩ := hx
    rw [← hpx]
    change Ideal.quotientEquivAlg J.toIdeal I.toIdeal
      (linearSubstitutionEquiv M hM).symm
      (linearCoordinateChange_ideal_symm M hM I J hIJ)
      (Ideal.Quotient.mk J.toIdeal p) ∈ grading I n
    rw [Ideal.quotientEquivAlg_mk]
    exact ⟨(linearSubstitutionEquiv M hM).symm p,
      homogeneous_equiv_symm (linearSubstitutionEquiv M hM)
        (fun _ q hq => linearSubstitution_homogeneous M hq) n hp, rfl⟩

/-- The explicit inverse agrees with the inverse of the forward quotient
coordinate equivalence. -/
theorem linearCoordinateChangeGradedHomSymm_apply
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (x : CoordinateRing J) :
    linearCoordinateChangeGradedHomSymm M hM I J hIJ x =
      (Ideal.quotientEquivAlg I.toIdeal J.toIdeal
        (linearSubstitutionEquiv M hM) hIJ).symm x := by
  have hIJ' : J.toIdeal = I.toIdeal.map
      (↑(linearSubstitutionEquiv M hM) : MvPolynomial (Fin 4) K →+*
        MvPolynomial (Fin 4) K) := by
    simpa using hIJ
  change Ideal.quotientEquivAlg J.toIdeal I.toIdeal
      (linearSubstitutionEquiv M hM).symm
      (linearCoordinateChange_ideal_symm M hM I J hIJ) x = _
  rw [← Ideal.quotientEquivAlg_symm J.toIdeal (linearSubstitutionEquiv M hM) hIJ']

/-- The forward graded coordinate map fixes ground-field constants. -/
theorem linearCoordinateChangeGradedHom_base
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (a : K) :
    linearCoordinateChangeGradedHom M hM I J hIJ
      (algebraMap K (CoordinateRing I) a) = algebraMap K (CoordinateRing J) a := by
  have hIJ' : J.toIdeal = I.toIdeal.map
      (↑(linearSubstitutionEquiv M hM) : MvPolynomial (Fin 4) K →+*
        MvPolynomial (Fin 4) K) := by
    simpa using hIJ
  change Ideal.quotientEquivAlg I.toIdeal J.toIdeal
      (linearSubstitutionEquiv M hM) hIJ' (Ideal.Quotient.mk I.toIdeal (C a)) =
    Ideal.Quotient.mk J.toIdeal (C a)
  rw [Ideal.quotientEquivAlg_mk]
  exact congrArg (Ideal.Quotient.mk J.toIdeal)
    ((linearSubstitutionEquiv M hM).commutes a)

/-- The inverse graded coordinate map also fixes ground-field constants. -/
theorem linearCoordinateChangeGradedHomSymm_base
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (a : K) :
    linearCoordinateChangeGradedHomSymm M hM I J hIJ
      (algebraMap K (CoordinateRing J) a) = algebraMap K (CoordinateRing I) a := by
  change Ideal.quotientEquivAlg J.toIdeal I.toIdeal
      (linearSubstitutionEquiv M hM).symm
      (linearCoordinateChange_ideal_symm M hM I J hIJ)
      (Ideal.Quotient.mk J.toIdeal (C a)) = Ideal.Quotient.mk I.toIdeal (C a)
  rw [Ideal.quotientEquivAlg_mk]
  exact congrArg (Ideal.Quotient.mk I.toIdeal)
    ((linearSubstitutionEquiv M hM).symm.commutes a)

/-- The forward coordinate change preserves the coefficient map on every
homogeneous affine chart. -/
theorem linearCoordinateChangeGradedHom_away_base
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (s : CoordinateRing I) :
    (Away.map (linearCoordinateChangeGradedHom M hM I J hIJ) s).comp
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := s)) =
    AllCharacteristics.GradedChart.baseMap (grading J)
      (z := linearCoordinateChangeGradedHom M hM I J hIJ s) := by
  apply RingHom.ext
  intro a
  apply val_injective
  change Localization.mk (linearCoordinateChangeGradedHom M hM I J hIJ
      (algebraMap K (CoordinateRing I) a))
      ⟨linearCoordinateChangeGradedHom M hM I J hIJ 1, _⟩ =
    Localization.mk (algebraMap K (CoordinateRing J) a) 1
  rw [linearCoordinateChangeGradedHom_base]
  exact congrArg (Localization.mk (algebraMap K (CoordinateRing J) a))
    (Subtype.ext (map_one (linearCoordinateChangeGradedHom M hM I J hIJ)))

/-- The inverse coordinate change preserves the coefficient map on every
homogeneous affine chart. -/
theorem linearCoordinateChangeGradedHomSymm_away_base
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (s : CoordinateRing J) :
    (Away.map (linearCoordinateChangeGradedHomSymm M hM I J hIJ) s).comp
      (AllCharacteristics.GradedChart.baseMap (grading J) (z := s)) =
    AllCharacteristics.GradedChart.baseMap (grading I)
      (z := linearCoordinateChangeGradedHomSymm M hM I J hIJ s) := by
  apply RingHom.ext
  intro a
  apply val_injective
  change Localization.mk (linearCoordinateChangeGradedHomSymm M hM I J hIJ
      (algebraMap K (CoordinateRing J) a))
      ⟨linearCoordinateChangeGradedHomSymm M hM I J hIJ 1, _⟩ =
    Localization.mk (algebraMap K (CoordinateRing I) a) 1
  rw [linearCoordinateChangeGradedHomSymm_base]
  exact congrArg (Localization.mk (algebraMap K (CoordinateRing I) a))
    (Subtype.ext (map_one (linearCoordinateChangeGradedHomSymm M hM I J hIJ)))

/-- The two explicit graded maps are mutually inverse. -/
theorem linearCoordinateChangeGradedHomSymm_comp
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom) :
    (linearCoordinateChangeGradedHomSymm M hM I J hIJ).comp
      (linearCoordinateChangeGradedHom M hM I J hIJ) = GradedRingHom.id (grading I) := by
  apply GradedRingHom.ext
  intro x
  change linearCoordinateChangeGradedHomSymm M hM I J hIJ
      (Ideal.quotientEquivAlg I.toIdeal J.toIdeal
        (linearSubstitutionEquiv M hM) hIJ x) = x
  rw [linearCoordinateChangeGradedHomSymm_apply]
  exact (Ideal.quotientEquivAlg I.toIdeal J.toIdeal
    (linearSubstitutionEquiv M hM) hIJ).symm_apply_apply x

theorem linearCoordinateChangeGradedHom_comp_symm
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom) :
    (linearCoordinateChangeGradedHom M hM I J hIJ).comp
      (linearCoordinateChangeGradedHomSymm M hM I J hIJ) = GradedRingHom.id (grading J) := by
  apply GradedRingHom.ext
  intro x
  change Ideal.quotientEquivAlg I.toIdeal J.toIdeal
      (linearSubstitutionEquiv M hM) hIJ
      (linearCoordinateChangeGradedHomSymm M hM I J hIJ x) = x
  rw [linearCoordinateChangeGradedHomSymm_apply]
  exact (Ideal.quotientEquivAlg I.toIdeal J.toIdeal
    (linearSubstitutionEquiv M hM) hIJ).apply_symm_apply x

/-- An invertible linear coordinate change carrying `I` to `J` induces an
isomorphism of their projective schemes. -/
noncomputable def linearCoordinateChangeSchemeIso
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom) :
    scheme I ≅ scheme J := by
  let F := linearCoordinateChangeGradedHom M hM I J hIJ
  let G := linearCoordinateChangeGradedHomSymm M hM I J hIJ
  have hF : Function.Surjective F := by
    intro y
    refine ⟨G y, ?_⟩
    have h := congrArg (fun q : grading J →+*ᵍ grading J => q y)
      (linearCoordinateChangeGradedHom_comp_symm M hM I J hIJ)
    simpa [F, G] using h
  have hG : Function.Surjective G := by
    intro x
    refine ⟨F x, ?_⟩
    have h := congrArg (fun q : grading I →+*ᵍ grading I => q x)
      (linearCoordinateChangeGradedHomSymm_comp M hM I J hIJ)
    simpa [F, G] using h
  let hF' := gradedSurjective_irrelevant_le F hF
  let hG' := gradedSurjective_irrelevant_le G hG
  refine
    { hom := Proj.map G hG'
      inv := Proj.map F hF'
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · change Proj.map G hG' ≫ Proj.map F hF' = 𝟙 (Proj (grading I))
    rw [← Proj.map_comp F G hF' hG']
    have hcomp : G.comp F = GradedRingHom.id (grading I) := by
      simpa [F, G] using linearCoordinateChangeGradedHomSymm_comp M hM I J hIJ
    simpa only [hcomp] using (Proj.map_id (𝒜 := grading I))
  · change Proj.map F hF' ≫ Proj.map G hG' = 𝟙 (Proj (grading J))
    rw [← Proj.map_comp G F hG' hF']
    have hcomp : F.comp G = GradedRingHom.id (grading J) := by
      simpa [F, G] using linearCoordinateChangeGradedHom_comp_symm M hM I J hIJ
    simpa only [hcomp] using (Proj.map_id (𝒜 := grading J))

/-- The scheme isomorphism induced by a linear coordinate change is over the
coefficient field. -/
theorem linearCoordinateChangeSchemeIso_hom_toBase
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom) :
    (linearCoordinateChangeSchemeIso M hM I J hIJ).hom ≫ toBase J = toBase I := by
  let F := linearCoordinateChangeGradedHom M hM I J hIJ
  let G := linearCoordinateChangeGradedHomSymm M hM I J hIJ
  have hF : Function.Surjective F := by
    intro y
    refine ⟨G y, ?_⟩
    have h := congrArg (fun q : grading J →+*ᵍ grading J => q y)
      (linearCoordinateChangeGradedHom_comp_symm M hM I J hIJ)
    simpa [F, G] using h
  have hG : Function.Surjective G := by
    intro x
    refine ⟨F x, ?_⟩
    have h := congrArg (fun q : grading I →+*ᵍ grading I => q x)
      (linearCoordinateChangeGradedHomSymm_comp M hM I J hIJ)
    simpa [F, G] using h
  let hG' := gradedSurjective_irrelevant_le G hG
  let bI : Proj (grading I) ⟶ Spec (.of K) := toBase I
  let bJ : Proj (grading J) ⟶ Spec (.of K) := toBase J
  change Proj.map G hG' ≫ bJ = bI
  apply (Proj.mapAffineOpenCover G hG').openCover.hom_ext
  intro s
  change (Σ d : PNat, grading J d) at s
  obtain ⟨⟨d, hd⟩, s, hs⟩ := s
  change s ∈ grading J d at hs
  change Proj.awayι (grading I) (G s) (G.2 hs) hd ≫
      (Proj.map G hG' ≫ bJ) =
    Proj.awayι (grading I) (G s) (G.2 hs) hd ≫ bI
  have hbJ : Proj.awayι (grading J) s hs hd ≫ bJ =
      Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap (grading J) (z := s))) :=
    homogeneousChart_toBase J s hs hd
  have hbI : Proj.awayι (grading I) (G s) (G.2 hs) hd ≫ bI =
      Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := G s))) :=
    homogeneousChart_toBase I (G s) (G.2 hs) hd
  rw [← Category.assoc, Proj.awayι_comp_map G hG' hd s hs, Category.assoc,
    hbJ, hbI, ← Spec.map_comp]
  apply congrArg Spec.map
  rw [← CommRingCat.ofHom_comp]
  exact congrArg CommRingCat.ofHom
    (by simpa [G] using linearCoordinateChangeGradedHomSymm_away_base M hM I J hIJ s)

end PfaffianDescent
