import PfaffianDescent.CorayOriginalNativeNormalizedDerivationJetDictionary

/-! Original coefficient polynomial derivation and literal normalized
minor numerator algebra. These bounded helpers support spreading the
actual native generic minor; no original good open is claimed here. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial TrivSqZeroExt
universe u

/-- Canonical fulljet evaluation proves the multivariable derivative
formula with the actual original coefficient hom. -/
theorem derivation_polynomial_eval₂_direction001
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (d : Derivation K F (Fin 2 → F)) (z : Fin 4 → F)
    (q : MvPolynomial (Fin 4) K) (r : Fin 2) :
    d (q.eval₂ (algebraMap K F) z) r =
      ∑ i : Fin 4, (pderiv i q).eval₂ (algebraMap K F) z * d (z i) r := by
  let ell := derivationFieldFullJet d
  let v : Fin 2 → Fin 4 → F := fun t i => d (z i) t
  have hcoeff : ell.comp (algebraMap K F) = algebraMap K (SurfacePlaneJet F) := by
    apply RingHom.ext
    intro c
    exact derivationFieldFullJet_base001 d c
  have hcoords : (fun i => ell (z i)) = surfacePlaneJetCoordinates z v := by
    funext i
    apply TrivSqZeroExt.ext
    · change z i = (surfacePlaneJetCoordinates z v i).fst
      simp only [surfacePlaneJetCoordinates, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · change d (z i) = (surfacePlaneJetCoordinates z v i).snd
      simp only [surfacePlaneJetCoordinates, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, v]
  have h := MvPolynomial.hom_eval₂ q (algebraMap K F) ell z
  rw [hcoeff, hcoords] at h
  have hs := congrArg (fun w : SurfacePlaneJet F => w.snd r) h
  change d (q.eval₂ (algebraMap K F) z) r = _ at hs
  rw [surfacePlaneJet_tangent_value_eq_directional_derivative] at hs
  exact hs

/-- The quotient rule clears the actual pivot and projective denominator
using original ring numerator data. -/
theorem derivation_normalized_coordinate_eq_cleared001
    {K R F : Type u} [Field K] [CommRing R] [Field F] [Algebra K F]
    (g : R →+* F) (d : Derivation K F (Fin 2 → F))
    (G x y : R) (N P : Fin 2 → R)
    (hG : g G ≠ 0) (hy : g y ≠ 0)
    (hxD : ∀ r, d (g x) r = g (N r) / g G)
    (hyD : ∀ r, d (g y) r = g (P r) / g G) (r : Fin 2) :
    d (g x / g y) r = g (N r * y - x * P r) / (g G * g y ^ 2) := by
  rw [d.leibniz_div]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [hxD r, hyD r, map_sub, map_mul, map_mul]
  field_simp [hG, hy]
  <;> ring

/-- The literal original-ring normalized minor numerator. -/
def normalizedProjectionMinorNumerator
    {R : Type u} [CommRing R] (x y a : R) (Nx Ny Na : Fin 2 → R) : R :=
  (Nx 0 * a - x * Na 0) * (Ny 1 * a - y * Na 1) -
    (Nx 1 * a - x * Na 1) * (Ny 0 * a - y * Na 0)

/-- A nonzero actual normalized generic derivative minor forces its
explicit original-ring numerator nonzero under the original evaluation.
The derivative-numerator formulas are consumed as separately derived
algebraic identities, not as a desired rank output. -/
theorem derivation_normalized_minor_originalNumerator_ne_zero001
    {K R F : Type u} [Field K] [CommRing R] [Field F] [Algebra K F]
    (g : R →+* F) (d : Derivation K F (Fin 2 → F))
    (G x y a : R) (Nx Ny Na : Fin 2 → R)
    (hG : g G ≠ 0) (ha : g a ≠ 0)
    (hxD : ∀ r, d (g x) r = g (Nx r) / g G)
    (hyD : ∀ r, d (g y) r = g (Ny r) / g G)
    (haD : ∀ r, d (g a) r = g (Na r) / g G)
    (hminor : d (g x / g a) 0 * d (g y / g a) 1 -
      d (g x / g a) 1 * d (g y / g a) 0 ≠ 0) :
    g (normalizedProjectionMinorNumerator x y a Nx Ny Na) ≠ 0 := by
  have hx (r : Fin 2) := derivation_normalized_coordinate_eq_cleared001 g d G x a Nx Na hG ha hxD haD r
  have hy (r : Fin 2) := derivation_normalized_coordinate_eq_cleared001 g d G y a Ny Na hG ha hyD haD r
  intro hzero
  apply hminor
  rw [hx 0, hy 1, hx 1, hy 0]
  have hclear :
      g (Nx 0 * a - x * Na 0) * g (Ny 1 * a - y * Na 1) -
        g (Nx 1 * a - x * Na 1) * g (Ny 0 * a - y * Na 0) = 0 := by
    simpa only [normalizedProjectionMinorNumerator, map_sub, map_mul] using hzero
  rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, hclear, zero_div]

end PfaffianDescent.Coray
end
