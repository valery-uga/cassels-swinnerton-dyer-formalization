import AllCharacteristics.AffineFlatImage
import AllCharacteristics.IdealSheafOpenExt

/-! # Scheme-theoretic image under affine flat base change

For an affine morphism and an affine flat change of base, the actual image
ideal pulls back to the image ideal of the Cartesian base change. The proof
uses affine neighborhoods in the original target and the established affine
ring-kernel calculation. This applies to finite étale quotient covers.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AllCharacteristics
universe u

/-- The kernel ideal of the canonical base change is the actual pullback
ideal under an affine flat morphism. -/
lemma kernel_pullback_snd_of_affine_flat
    {X Y Y' : Scheme.{u}} (i : X ⟶ Y) [IsAffineHom i]
    (g : Y' ⟶ Y) [IsAffineHom g] [Flat g] :
    (pullback.snd i g).ker = i.ker.comap g := by
  let W : Y.affineOpens → Y'.affineOpens := fun U => ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩
  apply idealSheaf_ext_of_comap_affine_cover W
  · change (⨆ U : Y.affineOpens, g ⁻¹ᵁ U.1) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  intro U
  let V := i ⁻¹ᵁ U.1
  let s := i ∣_ U.1
  let r := g ∣_ U.1
  let j := (W U).1.ι
  have hres_i := (isPullback_morphismRestrict i U.1).flip
  have hres_g := (isPullback_morphismRestrict g U.1).flip
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.toScheme := U.2.preimage i
  have : IsAffine (W U).1.toScheme := (W U).2
  have : Flat r := MorphismProperty.of_isPullback (P := @Flat.{u}) hres_g inferInstance
  have hlocal : IsPullback (pullback.fst s r) (pullback.snd s r) s r :=
    IsPullback.of_hasPullback _ _
  have houter : IsPullback (pullback.fst s r ≫ V.ι) (pullback.snd s r) i (j ≫ g) := by
    have h := hlocal.paste_horiz hres_i
    have he : r ≫ U.1.ι = j ≫ g := hres_g.w.symm
    rw [he] at h
    exact h
  let k : pullback s r ⟶ pullback i g :=
    pullback.lift (pullback.fst s r ≫ V.ι) (pullback.snd s r ≫ j)
      (houter.w.trans (Category.assoc _ _ _).symm)
  have hbc : IsPullback k (pullback.snd s r) (pullback.snd i g) j := by
    have houter' : IsPullback (k ≫ pullback.fst i g) (pullback.snd s r) i (j ≫ g) := by
      rw [show k ≫ pullback.fst i g = pullback.fst s r ≫ V.ι from pullback.lift_fst _ _ _]
      exact houter
    exact houter'.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback i g)
  have h₁ := kernel_of_open_pullback hbc
  have h₂ := kernel_of_open_pullback hres_i
  have h₃ := kernel_of_affine_flat_pullback hlocal
  change (pullback.snd i g).ker.comap j = (i.ker.comap g).comap j
  rw [← h₁, ← Scheme.IdealSheafData.comap_comp, hres_g.w,
    Scheme.IdealSheafData.comap_comp, ← h₂]
  exact h₃

/-- Scheme-theoretic image commutes with affine flat base change in any
actual Cartesian square with an affine original morphism. -/
lemma kernel_of_affine_flat_baseChange
    {P X Y Y' : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y'}
    {i : X ⟶ Y} [IsAffineHom i] {g : Y' ⟶ Y} [IsAffineHom g] [Flat g]
    (h : IsPullback a b i g) : b.ker = i.ker.comap g := by
  rw [← h.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso]
  exact kernel_pullback_snd_of_affine_flat i g

end AllCharacteristics
