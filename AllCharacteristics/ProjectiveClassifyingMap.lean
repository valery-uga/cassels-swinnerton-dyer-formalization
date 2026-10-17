import AllCharacteristics.ProjectiveEquationIndependence
import AllCharacteristics.UniversalProjectiveEquationFiber

/-!
# The coefficient-independent projective classifying map

A nonzero homogeneous equation has a classifying morphism to projective
coefficient space. Its equality with every normalized chart construction is
proved, so its definition is independent of the coefficient chosen internally.
The actual universal fiber is the original hypersurface over its given field.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R k : Type u} [CommRing R] [Field k] {σ : Type} {d : ℕ}
variable (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (hne : p ≠ 0)

/-- Choose a nonzero coefficient to define the classifying morphism; subsequent
identities prove that the resulting morphism is independent of this choice. -/
noncomputable def chosenEquationCoefficient : Monomials σ d :=
  Classical.choose (homogeneous_exists_nonzero_coefficient p hp hne)

/-- The internally chosen coefficient is nonzero. -/
theorem chosenEquationCoefficient_ne_zero :
    p.coeff (chosenEquationCoefficient p hp hne).1 ≠ 0 :=
  Classical.choose_spec (homogeneous_exists_nonzero_coefficient p hp hne)

variable (b : R →+* k)

/-- The projective classifying morphism of a nonzero homogeneous field equation. -/
noncomputable def projectiveClassifyingMap : Spec (.of k) ⟶ projectiveParameters R σ d :=
  projectiveEquationParameter b p (chosenEquationCoefficient p hp hne)
    (chosenEquationCoefficient_ne_zero p hp hne)

/-- Every nonzero coefficient gives exactly the same classifying morphism. -/
theorem projectiveClassifyingMap_eq_chart (j : Monomials σ d) (hj : p.coeff j.1 ≠ 0) :
    projectiveClassifyingMap p hp hne b = projectiveEquationParameter b p j hj :=
  projectiveEquationParameter_independent b p (chosenEquationCoefficient p hp hne) j
    (chosenEquationCoefficient_ne_zero p hp hne) hj

/-- The classifying morphism is over the original coefficient-ring map. -/
theorem projectiveClassifyingMap_toBase :
    projectiveClassifyingMap p hp hne b ≫ projectiveParametersToBase R σ d =
      Spec.map (CommRingCat.ofHom b) :=
  projectiveEquationParameter_toBase b p (chosenEquationCoefficient p hp hne)
    (chosenEquationCoefficient_ne_zero p hp hne)

variable [Finite σ]

/-- The original hypersurface is the actual universal fiber at its
coefficient-independent classifying morphism. -/
noncomputable def projectiveClassifyingFiberIso :
    hypersurface p hp ≅ pullback (projectiveUniversalToBase R σ d)
      (projectiveClassifyingMap p hp hne b) :=
  projectiveEquationFiberIso b p (chosenEquationCoefficient p hp hne)
    (chosenEquationCoefficient_ne_zero p hp hne) hp

/-- The coefficient-independent fiber identification preserves the original field. -/
theorem projectiveClassifyingFiberIso_hom_snd :
    (projectiveClassifyingFiberIso p hp hne b).hom ≫
      pullback.snd (projectiveUniversalToBase R σ d) (projectiveClassifyingMap p hp hne b) =
        hypersurfaceToBase p hp :=
  projectiveEquationFiberIso_hom_snd b p (chosenEquationCoefficient p hp hne)
    (chosenEquationCoefficient_ne_zero p hp hne) hp

/-- The coefficient-independent fiber identification maps to the universal
family through the concrete normalized-chart reduction of the equation. -/
theorem projectiveClassifyingFiberIso_hom_fst :
    (projectiveClassifyingFiberIso p hp hne b).hom ≫
      pullback.fst (projectiveUniversalToBase R σ d)
      (projectiveClassifyingMap p hp hne b) =
        projectiveEquationFiberToUniversalFamily b p
          (chosenEquationCoefficient p hp hne)
          (chosenEquationCoefficient_ne_zero p hp hne) hp := by
  change ((projectiveEquationChartFiberIso b p
      (chosenEquationCoefficient p hp hne)
      (chosenEquationCoefficient_ne_zero p hp hne) hp).hom ≫
    (isPullback_globalFamily_equationParameter b p
      (chosenEquationCoefficient p hp hne)
      (chosenEquationCoefficient_ne_zero p hp hne)).isoPullback.hom) ≫
      pullback.fst (projectiveUniversalToBase R σ d)
        (projectiveEquationParameter b p
          (chosenEquationCoefficient p hp hne)
          (chosenEquationCoefficient_ne_zero p hp hne)) = _
  rw [Category.assoc, IsPullback.isoPullback_hom_fst,
    ← Category.assoc, projectiveEquationChartFiberIso_hom_fst]
  rfl

/-- A field-valued universal-family point over an equation's classifying map
canonically lifts to a point of that equation's hypersurface. -/
noncomputable def projectiveClassifyingFiberLift
    (q : Spec (.of k) ⟶ projectiveUniversalFamily R σ d)
    (hq : q ≫ projectiveUniversalToBase R σ d =
      projectiveClassifyingMap p hp hne b) :
    Spec (.of k) ⟶ hypersurface p hp :=
  pullback.lift q (𝟙 _) (by simpa only [Category.id_comp] using hq) ≫
    (projectiveClassifyingFiberIso p hp hne b).inv

/-- The canonical lift of a universal-family point over a classifying map is
over the identity of the equation's coefficient field. -/
theorem projectiveClassifyingFiberLift_comp_toBase
    (q : Spec (.of k) ⟶ projectiveUniversalFamily R σ d)
    (hq : q ≫ projectiveUniversalToBase R σ d =
      projectiveClassifyingMap p hp hne b) :
    projectiveClassifyingFiberLift p hp hne b q hq ≫ hypersurfaceToBase p hp =
      𝟙 _ := by
  unfold projectiveClassifyingFiberLift
  rw [← projectiveClassifyingFiberIso_hom_snd (R := R) p hp hne b, Category.assoc,
    Iso.inv_hom_id_assoc, pullback.lift_snd]

/-- The canonical lift maps back to the given universal-family point through
the concrete equation fiber map. -/
theorem projectiveClassifyingFiberLift_comp_toUniversalFamily
    (q : Spec (.of k) ⟶ projectiveUniversalFamily R σ d)
    (hq : q ≫ projectiveUniversalToBase R σ d =
      projectiveClassifyingMap p hp hne b) :
    projectiveClassifyingFiberLift p hp hne b q hq ≫
      projectiveEquationFiberToUniversalFamily b p
        (chosenEquationCoefficient p hp hne)
        (chosenEquationCoefficient_ne_zero p hp hne) hp = q := by
  unfold projectiveClassifyingFiberLift
  rw [← projectiveClassifyingFiberIso_hom_fst (R := R) p hp hne b, Category.assoc,
    Iso.inv_hom_id_assoc, pullback.lift_fst]

/-- The hypersurface point lifted from a universal-family point has exactly
the same ambient projective point after the coefficient field change. -/
theorem projectiveClassifyingFiberLift_comp_toAmbient
    (q : Spec (.of k) ⟶ projectiveUniversalFamily R σ d)
    (hq : q ≫ projectiveUniversalToBase R σ d =
      projectiveClassifyingMap p hp hne b) :
    projectiveClassifyingFiberLift p hp hne b q hq ≫
      hypersurfaceToAmbient p hp ≫ ambientCoefficientMap b =
        q ≫ projectiveUniversalToAmbient R σ d := by
  rw [← projectiveEquationFiberToUniversalFamily_comp_toAmbient b p
    (chosenEquationCoefficient p hp hne)
    (chosenEquationCoefficient_ne_zero p hp hne) hp,
    ← Category.assoc,
    projectiveClassifyingFiberLift_comp_toUniversalFamily p hp hne b q hq]

/-- A field-valued universal-family point over an equation's classifying map
supplies nonzero homogeneous coordinates that solve that equation. -/
theorem projectiveClassifyingFiberLift_coordinates
    (q : Spec (.of k) ⟶ projectiveUniversalFamily R σ d)
    (hq : q ≫ projectiveUniversalToBase R σ d =
      projectiveClassifyingMap p hp hne b) :
    ∃ v : σ → k, v ≠ 0 ∧ p.eval v = 0 := by
  obtain ⟨v, hv, he⟩ := hypersurface_coordinates_of_point (RingHom.id k) p hp
    (projectiveClassifyingFiberLift p hp hne b q hq) (by
      simpa only [show CommRingCat.ofHom (RingHom.id k) = 𝟙 _ by rfl,
        Spec.map_id] using
        projectiveClassifyingFiberLift_comp_toBase p hp hne b q hq)
  exact ⟨v, hv, by simpa using he⟩

/-- A point of a nonzero homogeneous field equation belongs to the universal
incidence locus at its coefficient-independent projective classifying map. -/
theorem projectiveClassifyingIncidence_mem_range (x : hypersurface p hp) :
    Limits.prod.lift
      (hypersurfaceToAmbient p hp ≫ ambientCoefficientMap b)
      (hypersurfaceToBase p hp ≫ projectiveClassifyingMap p hp hne b) x ∈
      Set.range (projectiveUniversalIncidence R σ d) := by
  let i := chosenEquationCoefficient p hp hne
  have hi : p.coeff i.1 ≠ 0 := chosenEquationCoefficient_ne_zero p hp hne
  rw [projectiveClassifyingMap_eq_chart p hp hne b i hi]
  exact projectiveEquationIncidence_mem_range b p i hi hp x

end UniversalHomogeneous
end AllCharacteristics
