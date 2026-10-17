import AllCharacteristics.HypersurfaceCoefficientNaturality
import AllCharacteristics.OrderedConfigurationFieldPoints
import AllCharacteristics.HomogeneousConfigurationQuotient

/-! A coefficient extension does not identify field-valued points of a
projective hypersurface when they are viewed over the original field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Distinct points of a base-changed hypersurface over the extension field
remain distinct as extension-field-valued points of the original
hypersurface. This follows from the actual Cartesian base-change square. -/
theorem hypersurfaceCoefficientChange_injective_on_fieldPoints
    {K L : Type u} [Field K] [Field L]
    (b : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x y : Spec (.of L) ⟶ hypersurface (p.map b) (hp.map b))
    (hx : x ≫ hypersurfaceToBase (p.map b) (hp.map b) = 𝟙 _)
    (hy : y ≫ hypersurfaceToBase (p.map b) (hp.map b) = 𝟙 _)
    (heq : x ≫ projectiveCoefficientMap b (equationIdeal p hp)
        (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp) =
      y ≫ projectiveCoefficientMap b (equationIdeal p hp)
        (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp)) :
    x = y := by
  let e := hypersurfaceBaseChangeIso b p hp
  have hfst : x ≫ e.hom ≫
      pullback.fst (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)) =
      y ≫ e.hom ≫
        pullback.fst (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)) := by
    simp only [← Category.assoc, e, hypersurfaceBaseChangeIso_hom_fst]
    exact heq
  have hsnd : x ≫ e.hom ≫
      pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)) =
      y ≫ e.hom ≫
        pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)) := by
    simpa only [Category.assoc, e, hypersurfaceBaseChangeIso_hom_snd, hx, hy]
  have hpull : x ≫ e.hom = y ≫ e.hom := pullback.hom_ext hfst hsnd
  exact (cancel_mono e.hom).mp hpull

/-- Eight distinct extension-field points of the base-changed cubic form
an actual extension-field-valued ordered configuration of the original
cubic. The coordinate morphisms are exactly the coefficient-restricted
points, and the base map is the original field extension. -/
theorem exists_orderedCubicConfigurationFieldPoint_of_coefficientExtension
    {K L : Type u} [Field K] [Field L]
    (b : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 8 → (Spec (.of L) ⟶ hypersurface (p.map b) (hp.map b)))
    (hxbase : ∀ i, x i ≫ hypersurfaceToBase (p.map b) (hp.map b) = 𝟙 _)
    (hxdist : ∀ i j, i ≠ j → x i ≠ x j) :
    ∃ a : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left,
      a ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom =
        Spec.map (CommRingCat.ofHom b) ∧
      ∀ i, (a ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left =
        x i ≫ projectiveCoefficientMap b (equationIdeal p hp)
          (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp) := by
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  let f : hypersurface (p.map b) (hp.map b) ⟶ hypersurface p hp :=
    projectiveCoefficientMap b (equationIdeal p hp)
      (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp)
  have hfbase : f ≫ hypersurfaceToBase p hp =
      hypersurfaceToBase (p.map b) (hp.map b) ≫
        Spec.map (CommRingCat.ofHom b) := by
    exact projectiveCoefficientMap_toBase b (equationIdeal p hp)
      (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp)
  let q : Fin 8 → (Spec (.of L) ⟶ hypersurface p hp) := fun i => x i ≫ f
  have hqbase : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom b) := by
    intro i
    dsimp only [q]
    rw [Category.assoc, hfbase, ← Category.assoc,
      hxbase i]
    simp
  have hqdist : ∀ i j, i ≠ j → q i ≠ q j := by
    intro i j hij heq
    exact hxdist i j hij
      (hypersurfaceCoefficientChange_injective_on_fieldPoints b p hp
        (x i) (x j) (hxbase i) (hxbase j) heq)
  exact exists_orderedConfigurationFieldPoint
    (hypersurfaceToBase p hp) 8
    (Spec.map (CommRingCat.ofHom b)) q hqbase hqdist

/-- An actual ordered configuration over the extension-field cubic maps to
an ordered configuration of the original cubic over the same extension
field. The construction uses the eight prescribed coordinate points. -/
theorem exists_orderedCubicConfigurationFieldPoint_of_baseChangedConfiguration
    {K L : Type u} [Field K] [Field L]
    (b : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (aL : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase (p.map b) (hp.map b)) 8).left)
    (haL : aL ≫ (orderedFamilyConfigurationOver
      (hypersurfaceToBase (p.map b) (hp.map b)) 8).hom = 𝟙 _) :
    ∃ aK : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left,
      aK ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom =
        Spec.map (CommRingCat.ofHom b) ∧
      ∀ i, (aK ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left =
        ((aL ≫ Over.Hom.left (orderedFamilyConfigurationι
          (hypersurfaceToBase (p.map b) (hp.map b)) 8)) ≫
          (orderedFamilyCoordinate
            (hypersurfaceToBase (p.map b) (hp.map b)) 8 i).left) ≫
        projectiveCoefficientMap b (equationIdeal p hp)
          (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp) := by
  let fL := hypersurfaceToBase (p.map b) (hp.map b)
  letI : IsSeparated fL :=
    isSeparated_homogeneousToBase (equationIdeal (p.map b) (hp.map b))
  let x : Fin 8 → (Spec (.of L) ⟶ hypersurface (p.map b) (hp.map b)) :=
    fun i => (aL ≫ Over.Hom.left (orderedFamilyConfigurationι fL 8)) ≫
      (orderedFamilyCoordinate fL 8 i).left
  have hxbase : ∀ i, x i ≫ fL = 𝟙 _ := by
    intro i
    have hc : (orderedFamilyCoordinate fL 8 i).left ≫ fL =
        (orderedFamilyPowerOver fL 8).hom :=
      (orderedFamilyCoordinate fL 8 i).w
    have hι : Over.Hom.left (orderedFamilyConfigurationι fL 8) ≫
        (orderedFamilyPowerOver fL 8).hom =
        (orderedFamilyConfigurationOver fL 8).hom :=
      (orderedFamilyConfigurationι fL 8).w
    simpa only [x, Category.assoc, hc, hι] using haL
  have hxdist : ∀ i j, i ≠ j → x i ≠ x j := by
    intro i j hij
    exact orderedConfigurationFieldPoint_coordinates_ne fL 8 aL i j hij
  obtain ⟨aK, haK, hcoord⟩ :=
    exists_orderedCubicConfigurationFieldPoint_of_coefficientExtension
      b p hp x hxbase hxdist
  exact ⟨aK, haK, hcoord⟩

end PfaffianDescent
