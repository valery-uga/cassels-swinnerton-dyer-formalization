import PfaffianDescent.QuadraticSkewResidualDenominatorFieldNonvanishing
/-! SOURCE ONLY / UNVERIFIED. Original descended inverse fractions and
original descended residual coordinates give unit-scalar reconstruction.
The only nonvanishing input on the inverse domain is its ACTUAL Q value.
No mixed-secant, vector-reconstruction, or scheme-map certificate is assumed. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open MvPolynomial Module QuarticNet OriginalBridge AmbientResidual MixedNonvanishing
universe u
variable {k E L : Type u} [Field k] [Field E] [Field L]
variable [Algebra k E] [Algebra k L]

def originalInverseFieldParameters (w : Fin 4 → L)
    (Q R_T R_U : MvPolynomial (Fin 4) k) : SecantPlaneIndex → L :=
  fun i => ![R_T.eval₂ (algebraMap k L) w / Q.eval₂ (algebraMap k L) w,
    R_U.eval₂ (algebraMap k L) w / Q.eval₂ (algebraMap k L) w] i.down

theorem original_inverse_field_reconstructs_residual
    (C : Basis (Fin 4) E (Fin 4 → E)) (f : E →ₐ[k] L)
    (α β δ : E) (hαβ : α ≠ β) (hδ : δ ≠ 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hLeft : linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F) ∈
      Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)))
    (hRight : linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F) ∈
      Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E)))
    (r : Fin 4 → MvPolynomial SecantPlaneIndex k)
    (hr : ∀ i, MvPolynomial.map (algebraMap k E) (r i) = MvPolynomial.C δ *
      originalAmbientResidual C α β
        (linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)) i)
    (Q R_T R_U : MvPolynomial (Fin 4) k)
    (hQ : MvPolynomial.map (algebraMap k E) Q =
      pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2)
    (hT : MvPolynomial.map (algebraMap k E) R_T = MvPolynomial.C (α - β)⁻¹ *
      (MvPolynomial.C α * pairedInverseCoordinates C 3 * pairedInverseCoordinates C 0 -
        MvPolynomial.C β * pairedInverseCoordinates C 1 * pairedInverseCoordinates C 2))
    (hU : MvPolynomial.map (algebraMap k E) R_U = MvPolynomial.C (α - β)⁻¹ *
      (pairedInverseCoordinates C 1 * pairedInverseCoordinates C 2 -
        pairedInverseCoordinates C 3 * pairedInverseCoordinates C 0))
    (w : Fin 4 → L) (hFw : F.eval₂ (algebraMap k L) w = 0)
    (hQw : Q.eval₂ (algebraMap k L) w ≠ 0)
    (hQrecover : Q.eval₂ (algebraMap k L)
      (fun i => (r i).eval₂ (algebraMap k L) (originalInverseFieldParameters w Q R_T R_U)) ≠ 0) :
    ∃ c : L, c ≠ 0 ∧
      (fun i => (r i).eval₂ (algebraMap k L) (originalInverseFieldParameters w Q R_T R_U)) =
        c • w := by
  have hcoeff : f.toRingHom.comp (algebraMap k E) = algebraMap k L := by
    ext a
    exact f.commutes a
  let FE := MvPolynomial.map (algebraMap k E) F
  let G := linearSubstitution (basisCoordinateMatrix C) FE
  let v := pairedValues C f.toRingHom w
  have hv := descended_denominator_field_value_ne_zero C f.toRingHom Q hQ w
    (by rwa [hcoeff])
  have hnum := descended_inverse_numerators_field_values C f.toRingHom α β Q R_T R_U hQ hT hU w
  rw [hcoeff] at hnum
  have hparams : originalInverseFieldParameters w Q R_T R_U =
      (fun i => ![inverseT (f α) (f β) v, inverseU (f α) (f β) v] i.down) := by
    ext i
    rcases i with ⟨i⟩
    fin_cases i
    · exact hnum.1
    · exact hnum.2
  have hQrecover' : Q.eval₂ (f.toRingHom.comp (algebraMap k E))
      (fun i => (r i).eval₂ (f.toRingHom.comp (algebraMap k E))
        (fun j => ![inverseT (f α) (f β) v, inverseU (f α) (f β) v] j.down)) ≠ 0 := by
    rwa [hcoeff, ← hparams]
  have hB := recovered_rightSecant_at_inverseParameters_ne_zero
    C f.toRingHom α β δ hαβ G r hr Q hQ w hv.1 hv.2 hQrecover'
  have hFw' : FE.eval₂ f.toRingHom w = 0 := by
    rw [MvPolynomial.eval₂_map, hcoeff]
    exact hFw
  obtain ⟨c, hc, hrec⟩ := descended_original_residual_field_reconstruction C f.toRingHom
    α β δ hαβ hδ FE (hF.map _) hLeft hRight r hr w hFw' hv.1 hv.2 hB
  refine ⟨c, hc, ?_⟩
  have htransport :
      (fun i => (r i).eval₂ (algebraMap k L) (originalInverseFieldParameters w Q R_T R_U)) =
      (fun i => (r i).eval₂ (f.toRingHom.comp (algebraMap k E))
        (fun j => ![inverseT (f.toRingHom α) (f.toRingHom β) (pairedValues C f.toRingHom w),
          inverseU (f.toRingHom α) (f.toRingHom β) (pairedValues C f.toRingHom w)] j.down)) := by
    funext i
    exact congrArg₂ (fun (g : k →+* L) (s : SecantPlaneIndex → L) => (r i).eval₂ g s)
      hcoeff.symm hparams
  exact htransport.trans hrec

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
