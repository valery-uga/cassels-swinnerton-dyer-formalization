import PfaffianDescent.CubicElevenPointGenericJetWitness

/-! The actual common-chart linear form is a unit on all native localized
point and jet coordinates. This supplies whole-jet normalization on the
same ground-field chart as the actual eleven-point ideal. -/

noncomputable section
namespace PfaffianDescent

open MvPolynomial

universe u v
set_option backward.isDefEq.respectTransparency false

theorem cubicCoordinateFieldMap_linearForm_ne_zero
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4)
    (ell : MvPolynomial (Fin 4) R) (hell : ell.IsHomogeneous 1)
    (hellx : ∀ k, ell.eval (x k) = 1)
    (g : Localization.Away (cubicCoordinateDenominator x anchor) →+* F) (k : Fin 11) :
    aeval (fun j => g (cubicCoordinateLocalizedVector x anchor k j))
      (ell.map (g.comp (algebraMap R
        (Localization.Away (cubicCoordinateDenominator x anchor))))) ≠ 0 := by
  let h : R →+* F := g.comp (algebraMap R
    (Localization.Away (cubicCoordinateDenominator x anchor)))
  have hden : h (x k (anchor k)) ≠ 0 :=
    ((cubicCoordinateDenominator_isUnit_each x anchor k).map g).ne_zero
  have heval : aeval (fun j => h (x k j)) (ell.map h) = 1 := by
    change (eval (h ∘ x k)) (ell.map h) = 1
    rw [← MvPolynomial.map_eval, hellx, map_one]
  have hscale := cubicClosedPointSerreSurfaceJetCotangent_aeval_mul_homogeneous
    (ell.map h) (hell.map h) (h (x k (anchor k)))⁻¹ (fun j => h (x k j))
  have hcoords : (fun j => g (cubicCoordinateLocalizedVector x anchor k j)) =
      fun j => (h (x k (anchor k)))⁻¹ * h (x k j) :=
    funext (cubicCoordinateFieldMap_vector x anchor g k)
  change aeval _ (ell.map h) ≠ 0
  rw [hcoords, hscale, heval, pow_one, mul_one]
  exact inv_ne_zero hden

theorem cubicCoordinateFieldMap_linearForm_jet_isUnit
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (x : Fin 11 → Fin 4 → R) (anchor : Fin 11 → Fin 4)
    (ell : MvPolynomial (Fin 4) R) (hell : ell.IsHomogeneous 1)
    (hellx : ∀ k, ell.eval (x k) = 1)
    (g : Localization.Away (cubicCoordinateDenominator x anchor) →+* F)
    (rows : Fin 3 → Fin 4 → Fin 2 → F) (k : Fin 3) :
    IsUnit (aeval (cubicFullJetCoordinates
      (fun i j => g (cubicCoordinateLocalizedVector x anchor i j)) rows k)
      (ell.map (g.comp (algebraMap R
        (Localization.Away (cubicCoordinateDenominator x anchor)))))) := by
  apply cubicClosedPointSerreSurfaceJetCotangent_ell_jet_isUnit
  simpa [cubicFullJetCoordinates] using
    cubicCoordinateFieldMap_linearForm_ne_zero x anchor ell hell hellx g (k.castAdd 8)

end PfaffianDescent
