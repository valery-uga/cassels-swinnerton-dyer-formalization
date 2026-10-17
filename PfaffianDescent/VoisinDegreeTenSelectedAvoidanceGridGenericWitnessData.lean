import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericFinite
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

structure VoisinDegreeTenSelectedAvoidanceGridGenericFiniteWitness
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) where
  U : Scheme.{u}
  affine : IsAffine U
  integral : IsIntegral U
  i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
  openImmersion : IsOpenImmersion i
  t : Fin 16 → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
    (coordinate (equationIdeal p hp) 0))))
  b : K →+* Γ(U, ⊤)
  x : Fin 16 → Fin 4 → Γ(U, ⊤)
  hdom : IsDomain Γ(U, ⊤)
  baseMap : b = voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
    (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).hom)
  coordinates : x = (fun k z => pulledLinearChartCoordinate (equationIdeal p hp)
    (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) U (t k) z)
  markedPoints : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
    (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
    (by decide : 0 < 1) =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 16)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 16 k).left
  m : Fin 16 ↪ Monomials (Fin 4) 3
  hdet : homogeneousMinorDet m x ≠ 0
  finiteWitness :
    letI : IsDomain Γ(U, ⊤) := hdom
    let S := Localization.Away (homogeneousMinorDet m x)
    letI : IsDomain S := Localization.Away.isDomain hdet
    let g := algebraMap S (FractionRing S)
    let q := homogeneousMinorCorrectedPolynomial m x
      ((voisinDegreeTenSelectedAvoidance_gridCubic K 1).map b)
    let r := homogeneousMinorCorrectedPolynomial m x
      ((voisinDegreeTenSelectedAvoidance_gridCubic K 2).map b)
    (∀ k, (q.map g).eval (fun z => g (algebraMap Γ(U, ⊤) S (x k z))) = 0 ∧
      (r.map g).eval (fun z => g (algebraMap Γ(U, ⊤) S (x k z))) = 0) ∧
    IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (((p.map b).map (algebraMap Γ(U, ⊤) S)).map g)
      (q.map g) (r.map g)
      (((hp.map b).map (algebraMap Γ(U, ⊤) S)).map g)
      ((homogeneousMinorCorrectedPolynomial_isHomogeneous m x
        ((voisinDegreeTenSelectedAvoidance_gridCubic K 1).map b)
        ((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1).map b)).map g)
      ((homogeneousMinorCorrectedPolynomial_isHomogeneous m x
        ((voisinDegreeTenSelectedAvoidance_gridCubic K 2).map b)
        ((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2).map b)).map g)))

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_exists_gridGenericFiniteWitness
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    Nonempty (VoisinDegreeTenSelectedAvoidanceGridGenericFiniteWitness p hp) := by
  obtain ⟨U, hUa, hUi, i, t, b, x, hi, hdom, hb, hx, ht, _, _, hminor⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_sixteen_grid_generic_finite (L := L) p hp hno
  letI : IsDomain Γ(U, ⊤) := hdom
  obtain ⟨m, hdet, hfinite⟩ := hminor
  exact ⟨{
    U := U
    affine := hUa
    integral := hUi
    i := i
    openImmersion := hi
    t := t
    b := b
    x := x
    hdom := hdom
    baseMap := hb
    coordinates := hx
    markedPoints := ht
    m := m
    hdet := hdet
    finiteWitness := hfinite }⟩

end PfaffianDescent
