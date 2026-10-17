import PfaffianDescent.QuadraticSkewOriginalInverseFieldValues
/-! SOURCE ONLY / UNVERIFIED. The reconstruction scalar is nonzero on
the actual inverse domain because the original Q denominator is invertible
there. This removes any additional mixed-secant nonvanishing premise from
the field reconstruction caller. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open MvPolynomial Module OriginalBridge AmbientResidual ActualSecant MixedNonvanishing
universe u v
variable {k E : Type u} {L : Type v}
variable [Field k] [Field E] [Field L] [Algebra k E]

theorem ground_polynomial_eval_at_recovered
    (g : k →+* L) (s : SecantPlaneIndex → L)
    (r : Fin 4 → MvPolynomial SecantPlaneIndex k) (q : MvPolynomial (Fin 4) k) :
    (q.eval₂ MvPolynomial.C r).eval₂ g s =
      q.eval₂ g (fun i => (r i).eval₂ g s) := by
  have hcoeff : (MvPolynomial.eval₂Hom g s).comp MvPolynomial.C = g := by
    ext a
    simp
  change (MvPolynomial.eval₂Hom g s) (q.eval₂ MvPolynomial.C r) = _
  rw [MvPolynomial.hom_eval₂, hcoeff]
  exact congrArg (fun z : Fin 4 → L => q.eval₂ g z)
    (funext (fun i => congrFun (MvPolynomial.coe_eval₂Hom g s) (r i)))

theorem recovered_rightSecant_ne_zero
    (C : Basis (Fin 4) E (Fin 4 → E)) (f : E →+* L)
    (α β δ : E) (G : MvPolynomial (Fin 4) E)
    (r : Fin 4 → MvPolynomial SecantPlaneIndex k)
    (hr : ∀ i, MvPolynomial.map (algebraMap k E) (r i) =
      MvPolynomial.C δ * originalAmbientResidual C α β G i)
    (Q : MvPolynomial (Fin 4) k)
    (hQ : MvPolynomial.map (algebraMap k E) Q =
      pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2)
    (t u : L)
    (hQrecover : Q.eval₂ (f.comp (algebraMap k E))
      (fun i => (r i).eval₂ (f.comp (algebraMap k E)) (fun j => ![t, u] j.down)) ≠ 0) :
    rightMixedValue (mappedMixedCoefficients f G)
      1 (t + f α * u) 1 (t + f β * u) ≠ 0 := by
  have hpoly := congrArg (fun p : MvPolynomial SecantPlaneIndex E =>
    p.eval₂ f (fun j => ![t, u] j.down))
      (descended_inverse_denominator_evaluation C α β δ G r hr Q hQ)
  rw [MvPolynomial.eval₂_map, ground_polynomial_eval_at_recovered] at hpoly
  simp only [MvPolynomial.eval₂_neg, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_C] at hpoly
  rw [actualSecantB_eval₂] at hpoly
  intro hB
  apply hQrecover
  rw [hpoly, hB, mul_zero, neg_zero]

theorem recovered_rightSecant_at_inverseParameters_ne_zero
    (C : Basis (Fin 4) E (Fin 4 → E)) (f : E →+* L)
    (α β δ : E) (hαβ : α ≠ β) (G : MvPolynomial (Fin 4) E)
    (r : Fin 4 → MvPolynomial SecantPlaneIndex k)
    (hr : ∀ i, MvPolynomial.map (algebraMap k E) (r i) =
      MvPolynomial.C δ * originalAmbientResidual C α β G i)
    (Q : MvPolynomial (Fin 4) k)
    (hQ : MvPolynomial.map (algebraMap k E) Q =
      pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2)
    (w : Fin 4 → L) (hv₀ : pairedValues C f w 0 ≠ 0)
    (hv₂ : pairedValues C f w 2 ≠ 0)
    (hQrecover : Q.eval₂ (f.comp (algebraMap k E))
      (fun i => (r i).eval₂ (f.comp (algebraMap k E))
        (fun j => ![inverseT (f α) (f β) (pairedValues C f w),
          inverseU (f α) (f β) (pairedValues C f w)] j.down)) ≠ 0) :
    rightMixedValue (mappedMixedCoefficients f G)
      1 (pairedValues C f w 1 / pairedValues C f w 0)
      1 (pairedValues C f w 3 / pairedValues C f w 2) ≠ 0 := by
  have h := recovered_rightSecant_ne_zero C f α β δ G r hr Q hQ
    (inverseT (f α) (f β) (pairedValues C f w))
    (inverseU (f α) (f β) (pairedValues C f w)) hQrecover
  rwa [inverseT_add_left_mul_inverseU (f α) (f β)
    ((RingHom.injective f).ne hαβ) _ hv₀ hv₂,
    inverseT_add_right_mul_inverseU (f α) (f β)
    ((RingHom.injective f).ne hαβ) _ hv₀ hv₂] at h

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
