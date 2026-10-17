import AllCharacteristics.ConfigurationRationalCycleFamily
import AllCharacteristics.FiniteSubschemeRationalCycleFamily

/-!
# Finite subschemes along a configuration curve

Pulling the universal finite etale incidence subscheme along a projective-line
configuration curve gives an ideal-defined finite flat subscheme of the
projective family over that line.  The construction transports the nested
pullback to the standard projective-line pullback, so it can feed directly
into a finite-subscheme pencil.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PfaffianDescent

namespace AllCharacteristics
namespace HomogeneousProjective

universe u v

variable {A : Type u} [CommRing A]
variable {K : Type u} [Field K]
variable {sigma : Type v} [SetLike sigma A] [AddSubgroupClass sigma A]
variable (graded : ℕ → sigma) [GradedRing graded]
variable (f : Proj graded ⟶ Spec (.of K))

lemma configuration_pullback_congrHom_snd {X Y Z : Scheme.{u}} {f₁ f₂ : X ⟶ Z}
    {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom, pullback.map]

lemma configuration_pullback_congrHom_fst {X Y Z : Scheme.{u}} {f₁ f₂ : X ⟶ Z}
    {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.fst f₂ g₂ = pullback.fst f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom, pullback.map]

lemma IdealSheafData.subscheme_eqToIso_hom_subschemeι
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg (fun L ↦ L.subscheme) h)).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

/-- The universal finite incidence datum after its first, literal pullback
along the configuration curve. -/
noncomputable def projectiveConfigurationCurveIntermediateFiniteSubscheme
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    : FiniteSubschemeDatum
      (pullback.snd (pullback.snd f
        (projectiveConfigurationQuotientToBase graded f n)) c) n :=
  FiniteSubschemeDatum.baseChange
    (pullback.fst (pullback.snd f
      (projectiveConfigurationQuotientToBase graded f n)) c) c
    (IsPullback.of_hasPullback _ _) (projectiveConfigurationFiniteSubscheme graded f n)

/-- The ambient family pulled back along a configuration curve is the fixed
projective family over that line. -/
noncomputable def projectiveConfigurationCurveAmbientIso
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K) :
    pullback (pullback.snd f (projectiveConfigurationQuotientToBase graded f n)) c ≅
      pullback f (projectiveLineProjToBase K) :=
  pullbackLeftPullbackSndIso f (projectiveConfigurationQuotientToBase graded f n) c ≪≫
    pullback.congrHom rfl hc

lemma projectiveConfigurationCurveAmbientIso_hom_toLine
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K) :
    (projectiveConfigurationCurveAmbientIso graded f n c hc).hom ≫
      pullback.snd f (projectiveLineProjToBase K) =
    pullback.snd (pullback.snd f
      (projectiveConfigurationQuotientToBase graded f n)) c := by
  let q := projectiveConfigurationQuotientToBase graded f n
  let e := pullbackLeftPullbackSndIso f q c
  let r : pullback f (c ≫ q) ≅ pullback f (projectiveLineProjToBase K) :=
    pullback.congrHom rfl hc
  let p := pullback.snd f (projectiveLineProjToBase K)
  have hr : r.hom ≫ p = pullback.snd f (c ≫ q) := by
    simpa [r, p] using
      (configuration_pullback_congrHom_snd (f₁ := f) (g₁ := c ≫ q) rfl hc)
  calc
    (projectiveConfigurationCurveAmbientIso graded f n c hc).hom ≫ p =
        e.hom ≫ r.hom ≫ p := rfl
    _ = e.hom ≫ pullback.snd f (c ≫ q) := by rw [hr]
    _ = pullback.snd (pullback.snd f q) c := by simp [e]

lemma projectiveConfigurationCurveAmbientIso_hom_toProjective
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K) :
    (projectiveConfigurationCurveAmbientIso graded f n c hc).hom ≫
      pullback.fst f (projectiveLineProjToBase K) =
    pullback.fst (pullback.snd f
      (projectiveConfigurationQuotientToBase graded f n)) c ≫
      pullback.fst f (projectiveConfigurationQuotientToBase graded f n) := by
  let q := projectiveConfigurationQuotientToBase graded f n
  let e := pullbackLeftPullbackSndIso f q c
  let r : pullback f (c ≫ q) ≅ pullback f (projectiveLineProjToBase K) :=
    pullback.congrHom rfl hc
  let p := pullback.fst f (projectiveLineProjToBase K)
  have hr : r.hom ≫ p = pullback.fst f (c ≫ q) := by
    simpa [r, p] using
      (configuration_pullback_congrHom_fst (f₁ := f) (g₁ := c ≫ q) rfl hc)
  calc
    (projectiveConfigurationCurveAmbientIso graded f n c hc).hom ≫ p =
        e.hom ≫ r.hom ≫ p := rfl
    _ = e.hom ≫ pullback.fst f (c ≫ q) := by rw [hr]
    _ = pullback.fst (pullback.snd f q) c ≫ pullback.fst f q := by simp [e]

/-- The inverse ambient isomorphism forms the Cartesian change needed to
transport the pulled-back ideal to the standard family over the line. -/
theorem projectiveConfigurationCurveAmbientIsPullback
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K) :
    IsPullback (projectiveConfigurationCurveAmbientIso graded f n c hc).inv
      (pullback.snd f (projectiveLineProjToBase K))
      (pullback.snd (pullback.snd f
        (projectiveConfigurationQuotientToBase graded f n)) c) (𝟙 _) := by
  apply IsPullback.of_horiz_isIso
  refine ⟨?_⟩
  apply (cancel_epi (projectiveConfigurationCurveAmbientIso graded f n c hc).hom).1
  simpa using (projectiveConfigurationCurveAmbientIso_hom_toLine graded f n c hc).symm

/-- The universal rank-`n` incidence datum pulls back along a configuration
curve to an actual rank-`n` finite-subscheme datum of the fixed projective
family over the projective line. -/
noncomputable def projectiveConfigurationCurveFiniteSubscheme
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K) :
    FiniteSubschemeDatum (pullback.snd f (projectiveLineProjToBase K)) n :=
  FiniteSubschemeDatum.baseChange
    (projectiveConfigurationCurveAmbientIso graded f n c hc).inv (𝟙 _)
    (projectiveConfigurationCurveAmbientIsPullback graded f n c hc)
    (projectiveConfigurationCurveIntermediateFiniteSubscheme graded f n c)

/-- The datum from a configuration curve has the prescribed rank at every
projective-line point. -/
theorem projectiveConfigurationCurveFiniteSubscheme_finrank
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (x : projectiveLineProj K) :
    ((projectiveConfigurationCurveFiniteSubscheme graded f n c hc).val.subschemeι ≫
      pullback.snd f (projectiveLineProjToBase K)).finrank x = n :=
  (projectiveConfigurationCurveFiniteSubscheme graded f n c hc).property.2.2.2 x

/-- The finite subscheme transported from a configuration curve is étale over
the projective-line parameter.  This retains the reduced finite geometry of
the universal distinct-configuration incidence family, rather than only its
constant rank. -/
theorem etale_projectiveConfigurationCurveFiniteSubscheme_toLine
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K) :
    Etale ((projectiveConfigurationCurveFiniteSubscheme graded f n c hc).val.subschemeι ≫
      pullback.snd f (projectiveLineProjToBase K)) := by
  let q := projectiveConfigurationQuotientToBase graded f n
  let p := pullback.snd f q
  let a := pullback.fst p c
  let U := projectiveConfigurationFiniteSubscheme graded f n
  let Dn := projectiveConfigurationCurveIntermediateFiniteSubscheme graded f n c
  let e := projectiveConfigurationCurveAmbientIso graded f n c hc
  let D := projectiveConfigurationCurveFiniteSubscheme graded f n c hc
  let h₁ : IsPullback a (pullback.snd p c) p c := IsPullback.of_hasPullback p c
  let h₂ : IsPullback e.inv (pullback.snd f (projectiveLineProjToBase K))
      (pullback.snd p c) (𝟙 _) :=
    projectiveConfigurationCurveAmbientIsPullback graded f n c hc
  have hDn : Etale (Dn.val.subschemeι ≫ pullback.snd p c) := by
    change Etale ((FiniteSubschemeDatum.baseChange a c h₁ U).val.subschemeι ≫
      pullback.snd p c)
    exact MorphismProperty.of_isPullback (P := @Etale.{u})
      (isPullback_idealSubschemeFamily U.val a (pullback.snd p c) p c h₁)
      (by
        change Etale (projectiveConfigurationIncidenceToBase graded f n)
        infer_instance)
  change Etale ((FiniteSubschemeDatum.baseChange e.inv (𝟙 _) h₂ Dn).val.subschemeι ≫
    pullback.snd f (projectiveLineProjToBase K))
  exact MorphismProperty.of_isPullback (P := @Etale.{u})
    (isPullback_idealSubschemeFamily Dn.val e.inv
      (pullback.snd f (projectiveLineProjToBase K)) (pullback.snd p c) (𝟙 _) h₂)
    hDn

/-- Each marked endpoint of a configuration curve is a finite étale
subscheme of the fixed projective fiber.  This is the endpoint form used by
the degree-ten residual data, where reducedness must survive the movement
along the configuration curve. -/
theorem etale_projectiveConfigurationCurveFiniteSubschemeAtLineEndpoint_toBase
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    Etale ((finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) b).val.subschemeι ≫ f) :=
  etale_finiteSubschemeDatumAtLineEndpoint_toBase f n
    (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) b
    (etale_projectiveConfigurationCurveFiniteSubscheme_toLine graded f n c hc)

/-- Identifying an endpoint of a configuration curve with another
ideal-defined finite subscheme over the projective fiber transports its
étaleness to that chosen datum. -/
theorem etale_projectiveConfigurationCurveFiniteSubschemeAtLineEndpoint_of_iso_over
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool)
    (D : FiniteSubschemeDatum f n)
    (e : (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) b).val.subscheme ≅
        D.val.subscheme)
    (he : e.hom ≫ D.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) b).val.subschemeι) :
    Etale (D.val.subschemeι ≫ f) :=
  etale_finiteSubschemeDatum_of_iso_over f n
    (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) b)
    D e he
    (etale_projectiveConfigurationCurveFiniteSubschemeAtLineEndpoint_toBase
      graded f n c hc b)

/-- The subscheme in the standard projective-line pullback is canonically the
original incidence family pulled back along the configuration curve.  This
keeps the ideal-defined presentation and the incidence presentation of the
same finite flat family interchangeable. -/
noncomputable def projectiveConfigurationCurveFiniteSubschemeIso
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K) :
    (projectiveConfigurationCurveFiniteSubscheme graded f n c hc).val.subscheme ≅
      pullback (projectiveConfigurationIncidenceToBase graded f n) c := by
  let q := projectiveConfigurationQuotientToBase graded f n
  let g := pullback.snd f q
  let U := projectiveConfigurationFiniteSubscheme graded f n
  let a := pullback.fst g c
  let Dn := projectiveConfigurationCurveIntermediateFiniteSubscheme graded f n c
  have hDn : Dn.val = U.val.comap a :=
    FiniteSubschemeDatum.baseChange_ideal a c (IsPullback.of_hasPullback g c) U
  let i := projectiveConfigurationCurveAmbientIso graded f n c hc
  let D := projectiveConfigurationCurveFiniteSubscheme graded f n c hc
  have hD : D.val = Dn.val.comap i.inv :=
    FiniteSubschemeDatum.baseChange_ideal i.inv (𝟙 _)
      (projectiveConfigurationCurveAmbientIsPullback graded f n c hc) Dn
  let α₁ : D.val.subscheme ≅ (Dn.val.comap i.inv).subscheme :=
    eqToIso (congrArg (fun I ↦ I.subscheme) hD)
  let α : D.val.subscheme ≅ pullback i.inv Dn.val.subschemeι :=
    α₁ ≪≫ Dn.val.comapIso i.inv
  letI : IsIso i.inv := by
    dsimp [i, projectiveConfigurationCurveAmbientIso]
    infer_instance
  let β : pullback i.inv Dn.val.subschemeι ≅ Dn.val.subscheme :=
    asIso (pullback.snd i.inv Dn.val.subschemeι)
  let γ₁ : Dn.val.subscheme ≅ (U.val.comap a).subscheme :=
    eqToIso (congrArg (fun I ↦ I.subscheme) hDn)
  let γ : Dn.val.subscheme ≅ pullback a U.val.subschemeι :=
    γ₁ ≪≫ U.val.comapIso a
  let δ : pullback a U.val.subschemeι ≅ pullback U.val.subschemeι a :=
    pullbackSymmetry a U.val.subschemeι
  let ε : pullback U.val.subschemeι a ≅ pullback (U.val.subschemeι ≫ g) c :=
    pullbackRightPullbackFstIso g c U.val.subschemeι
  exact α ≪≫ β ≪≫ γ ≪≫ δ ≪≫ ε

lemma projectiveConfigurationCurveFiniteSubschemeIso_hom_toLine
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K) :
    (projectiveConfigurationCurveFiniteSubschemeIso graded f n c hc).hom ≫
      pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c =
    (projectiveConfigurationCurveFiniteSubscheme graded f n c hc).val.subschemeι ≫
      pullback.snd f (projectiveLineProjToBase K) := by
  let q := projectiveConfigurationQuotientToBase graded f n
  let g := pullback.snd f q
  let U := projectiveConfigurationFiniteSubscheme graded f n
  let a := pullback.fst g c
  let Dn := projectiveConfigurationCurveIntermediateFiniteSubscheme graded f n c
  have hDn : Dn.val = U.val.comap a :=
    FiniteSubschemeDatum.baseChange_ideal a c (IsPullback.of_hasPullback g c) U
  let i := projectiveConfigurationCurveAmbientIso graded f n c hc
  let D := projectiveConfigurationCurveFiniteSubscheme graded f n c hc
  have hD : D.val = Dn.val.comap i.inv :=
    FiniteSubschemeDatum.baseChange_ideal i.inv (𝟙 _)
      (projectiveConfigurationCurveAmbientIsPullback graded f n c hc) Dn
  let α₁ : D.val.subscheme ≅ (Dn.val.comap i.inv).subscheme :=
    eqToIso (congrArg (fun I ↦ I.subscheme) hD)
  let α : D.val.subscheme ≅ pullback i.inv Dn.val.subschemeι :=
    α₁ ≪≫ Dn.val.comapIso i.inv
  letI : IsIso i.inv := by
    dsimp [i, projectiveConfigurationCurveAmbientIso]
    infer_instance
  let β : pullback i.inv Dn.val.subschemeι ≅ Dn.val.subscheme :=
    asIso (pullback.snd i.inv Dn.val.subschemeι)
  let γ₁ : Dn.val.subscheme ≅ (U.val.comap a).subscheme :=
    eqToIso (congrArg (fun I ↦ I.subscheme) hDn)
  let γ : Dn.val.subscheme ≅ pullback a U.val.subschemeι :=
    γ₁ ≪≫ U.val.comapIso a
  let δ : pullback a U.val.subschemeι ≅ pullback U.val.subschemeι a :=
    pullbackSymmetry a U.val.subschemeι
  let ε : pullback U.val.subschemeι a ≅ pullback (U.val.subschemeι ≫ g) c :=
    pullbackRightPullbackFstIso g c U.val.subschemeι
  change (α ≪≫ β ≪≫ γ ≪≫ δ ≪≫ ε).hom ≫
      pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c =
    D.val.subschemeι ≫ pullback.snd f (projectiveLineProjToBase K)
  have hα : α.hom ≫ pullback.fst i.inv Dn.val.subschemeι = D.val.subschemeι := by
    simp only [α, Iso.trans_hom, Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
    exact IdealSheafData.subscheme_eqToIso_hom_subschemeι hD
  have hβ : β.hom ≫ Dn.val.subschemeι =
      pullback.fst i.inv Dn.val.subschemeι ≫ i.inv := by
    change pullback.snd i.inv Dn.val.subschemeι ≫ Dn.val.subschemeι = _
    exact pullback.condition.symm
  have hαβ : (α ≪≫ β).hom ≫ Dn.val.subschemeι = D.val.subschemeι ≫ i.inv := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [hβ, ← Category.assoc, hα]
  have hγ : γ.hom ≫ pullback.fst a U.val.subschemeι = Dn.val.subschemeι := by
    simp only [γ, Iso.trans_hom, Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
    exact IdealSheafData.subscheme_eqToIso_hom_subschemeι hDn
  have hδ : δ.hom ≫ pullback.snd U.val.subschemeι a =
      pullback.fst a U.val.subschemeι := by
    simpa [δ] using pullbackSymmetry_hom_comp_snd a U.val.subschemeι
  have hε : ε.hom ≫ pullback.snd (U.val.subschemeι ≫ g) c =
      pullback.snd U.val.subschemeι a ≫ pullback.snd g c := by
    exact pullbackRightPullbackFstIso_hom_snd g c U.val.subschemeι
  have hi : i.inv ≫ pullback.snd g c =
      pullback.snd f (projectiveLineProjToBase K) := by
    simpa [i, g] using
      (projectiveConfigurationCurveAmbientIsPullback graded f n c hc).w
  change (α ≪≫ β ≪≫ γ ≪≫ δ ≪≫ ε).hom ≫
      pullback.snd (U.val.subschemeι ≫ g) c =
    D.val.subschemeι ≫ pullback.snd f (projectiveLineProjToBase K)
  change α.hom ≫ β.hom ≫ γ.hom ≫ δ.hom ≫ ε.hom ≫
      pullback.snd (U.val.subschemeι ≫ g) c =
    D.val.subschemeι ≫ pullback.snd f (projectiveLineProjToBase K)
  have hδ' : δ.hom ≫
      (pullback.snd U.val.subschemeι a ≫ pullback.snd g c) =
      pullback.fst a U.val.subschemeι ≫ pullback.snd g c := by
    rw [← Category.assoc, hδ]
  have hγ' : γ.hom ≫
      (pullback.fst a U.val.subschemeι ≫ pullback.snd g c) =
      Dn.val.subschemeι ≫ pullback.snd g c := by
    rw [← Category.assoc, hγ]
  have hαβ' : α.hom ≫ (β.hom ≫
      (Dn.val.subschemeι ≫ pullback.snd g c)) =
      (D.val.subschemeι ≫ i.inv) ≫ pullback.snd g c := by
    change (α ≪≫ β).hom ≫ (Dn.val.subschemeι ≫ pullback.snd g c) = _
    rw [← Category.assoc, hαβ]
  rw [hε, hδ', hγ', hαβ', Category.assoc, hi]

lemma projectiveConfigurationCurveFiniteSubschemeIso_hom_toProjective
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K) :
    (projectiveConfigurationCurveFiniteSubschemeIso graded f n c hc).hom ≫
      pullback.fst (projectiveConfigurationIncidenceToBase graded f n) c ≫
        projectiveConfigurationIncidenceToProjective graded f n =
    (projectiveConfigurationCurveFiniteSubscheme graded f n c hc).val.subschemeι ≫
      pullback.fst f (projectiveLineProjToBase K) := by
  let q := projectiveConfigurationQuotientToBase graded f n
  let g := pullback.snd f q
  let U := projectiveConfigurationFiniteSubscheme graded f n
  let a := pullback.fst g c
  let Dn := projectiveConfigurationCurveIntermediateFiniteSubscheme graded f n c
  have hDn : Dn.val = U.val.comap a :=
    FiniteSubschemeDatum.baseChange_ideal a c (IsPullback.of_hasPullback g c) U
  let i := projectiveConfigurationCurveAmbientIso graded f n c hc
  let D := projectiveConfigurationCurveFiniteSubscheme graded f n c hc
  have hD : D.val = Dn.val.comap i.inv :=
    FiniteSubschemeDatum.baseChange_ideal i.inv (𝟙 _)
      (projectiveConfigurationCurveAmbientIsPullback graded f n c hc) Dn
  let α₁ : D.val.subscheme ≅ (Dn.val.comap i.inv).subscheme :=
    eqToIso (congrArg (fun I ↦ I.subscheme) hD)
  let α : D.val.subscheme ≅ pullback i.inv Dn.val.subschemeι :=
    α₁ ≪≫ Dn.val.comapIso i.inv
  letI : IsIso i.inv := by
    dsimp [i, projectiveConfigurationCurveAmbientIso]
    infer_instance
  let β : pullback i.inv Dn.val.subschemeι ≅ Dn.val.subscheme :=
    asIso (pullback.snd i.inv Dn.val.subschemeι)
  let γ₁ : Dn.val.subscheme ≅ (U.val.comap a).subscheme :=
    eqToIso (congrArg (fun I ↦ I.subscheme) hDn)
  let γ : Dn.val.subscheme ≅ pullback a U.val.subschemeι :=
    γ₁ ≪≫ U.val.comapIso a
  let δ : pullback a U.val.subschemeι ≅ pullback U.val.subschemeι a :=
    pullbackSymmetry a U.val.subschemeι
  let ε : pullback U.val.subschemeι a ≅ pullback (U.val.subschemeι ≫ g) c :=
    pullbackRightPullbackFstIso g c U.val.subschemeι
  change (α ≪≫ β ≪≫ γ ≪≫ δ ≪≫ ε).hom ≫
      pullback.fst (projectiveConfigurationIncidenceToBase graded f n) c ≫
        projectiveConfigurationIncidenceToProjective graded f n =
    D.val.subschemeι ≫ pullback.fst f (projectiveLineProjToBase K)
  have hα : α.hom ≫ pullback.fst i.inv Dn.val.subschemeι = D.val.subschemeι := by
    simp only [α, Iso.trans_hom, Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
    exact IdealSheafData.subscheme_eqToIso_hom_subschemeι hD
  have hβ : β.hom ≫ Dn.val.subschemeι =
      pullback.fst i.inv Dn.val.subschemeι ≫ i.inv := by
    change pullback.snd i.inv Dn.val.subschemeι ≫ Dn.val.subschemeι = _
    exact pullback.condition.symm
  have hαβ : (α ≪≫ β).hom ≫ Dn.val.subschemeι = D.val.subschemeι ≫ i.inv := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [hβ, ← Category.assoc, hα]
  have hγ : γ.hom ≫ pullback.fst a U.val.subschemeι = Dn.val.subschemeι := by
    simp only [γ, Iso.trans_hom, Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
    exact IdealSheafData.subscheme_eqToIso_hom_subschemeι hDn
  have hγsnd : γ.hom ≫ pullback.snd a U.val.subschemeι ≫ U.val.subschemeι =
      Dn.val.subschemeι ≫ a := by
    calc
      γ.hom ≫ pullback.snd a U.val.subschemeι ≫ U.val.subschemeι =
          γ.hom ≫ (pullback.snd a U.val.subschemeι ≫ U.val.subschemeι) := by
            rfl
      _ = γ.hom ≫ (pullback.fst a U.val.subschemeι ≫ a) := by
            rw [pullback.condition]
      _ = (γ.hom ≫ pullback.fst a U.val.subschemeι) ≫ a := by
            rw [Category.assoc]
      _ = Dn.val.subschemeι ≫ a := by rw [hγ]
  have hδ : δ.hom ≫ pullback.fst U.val.subschemeι a =
      pullback.snd a U.val.subschemeι := by
    simpa [δ] using pullbackSymmetry_hom_comp_fst a U.val.subschemeι
  have hε : ε.hom ≫ pullback.fst (U.val.subschemeι ≫ g) c =
      pullback.fst U.val.subschemeι a := by
    exact pullbackRightPullbackFstIso_hom_fst g c U.val.subschemeι
  have hi : i.inv ≫ a ≫ pullback.fst f q =
      pullback.fst f (projectiveLineProjToBase K) := by
    apply (cancel_epi i.hom).1
    calc
      i.hom ≫ (i.inv ≫ a ≫ pullback.fst f q) =
          (i.hom ≫ i.inv) ≫ a ≫ pullback.fst f q := by
            simp only [Category.assoc]
      _ = a ≫ pullback.fst f q := by simp
      _ = i.hom ≫ pullback.fst f (projectiveLineProjToBase K) := by
        simpa [i, a] using
          (projectiveConfigurationCurveAmbientIso_hom_toProjective graded f n c hc).symm
  change α.hom ≫ β.hom ≫ γ.hom ≫ δ.hom ≫ ε.hom ≫
      pullback.fst (U.val.subschemeι ≫ g) c ≫
        (U.val.subschemeι ≫ pullback.fst f q) =
    D.val.subschemeι ≫ pullback.fst f (projectiveLineProjToBase K)
  have hε' : ε.hom ≫ (pullback.fst (U.val.subschemeι ≫ g) c ≫
      (U.val.subschemeι ≫ pullback.fst f q)) =
      pullback.fst U.val.subschemeι a ≫ (U.val.subschemeι ≫ pullback.fst f q) := by
    rw [← Category.assoc, hε]
  have hδ' : δ.hom ≫ (pullback.fst U.val.subschemeι a ≫
      (U.val.subschemeι ≫ pullback.fst f q)) =
      pullback.snd a U.val.subschemeι ≫ (U.val.subschemeι ≫ pullback.fst f q) := by
    rw [← Category.assoc, hδ]
  have hγ' : γ.hom ≫ (pullback.snd a U.val.subschemeι ≫
      (U.val.subschemeι ≫ pullback.fst f q)) =
      Dn.val.subschemeι ≫ (a ≫ pullback.fst f q) := by
    simpa only [Category.assoc] using
      congrArg (fun t ↦ t ≫ pullback.fst f q) hγsnd
  have hαβ' : α.hom ≫ (β.hom ≫
      (Dn.val.subschemeι ≫ (a ≫ pullback.fst f q))) =
      D.val.subschemeι ≫ pullback.fst f (projectiveLineProjToBase K) := by
    calc
      α.hom ≫ (β.hom ≫ (Dn.val.subschemeι ≫ (a ≫ pullback.fst f q))) =
          (D.val.subschemeι ≫ i.inv) ≫ (a ≫ pullback.fst f q) := by
            simpa only [Iso.trans_hom, Category.assoc] using
              congrArg (fun t ↦ t ≫ (a ≫ pullback.fst f q)) hαβ
      _ = D.val.subschemeι ≫ pullback.fst f (projectiveLineProjToBase K) := by
            calc
              (D.val.subschemeι ≫ i.inv) ≫ (a ≫ pullback.fst f q) =
                  D.val.subschemeι ≫ (i.inv ≫ a ≫ pullback.fst f q) := by
                    simp only [Category.assoc]
              _ = D.val.subschemeι ≫ pullback.fst f (projectiveLineProjToBase K) := by
                    rw [hi]
  rw [hε', hδ', hγ', hαβ']

/-- The map between the actual finite-subscheme fiber and the incidence
fiber induced by the global family isomorphism. -/
noncomputable def projectiveConfigurationCurveFiniteSubschemeFiberMap
    [IsSeparated f]
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    (rationalCycleFamily_of_finiteSubschemeDatum f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc)).fiber b ⟶
      (rationalCycleFamily_of_configurationCurve graded f n c hc).fiber b := by
  let D := projectiveConfigurationCurveFiniteSubscheme graded f n c hc
  let e := projectiveConfigurationCurveFiniteSubschemeIso graded f n c hc
  let z := projectiveLineEndpoint K b
  exact pullback.map (D.val.subschemeι ≫ pullback.snd f (projectiveLineProjToBase K)) z
    (pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c) z
    e.hom (𝟙 _) (𝟙 _)
    (by
      simpa [D, e] using
        (projectiveConfigurationCurveFiniteSubschemeIso_hom_toLine graded f n c hc).symm)
    (by simp)

theorem projectiveConfigurationCurveFiniteSubschemeFiberMap_isIso
    [IsSeparated f]
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    IsIso (projectiveConfigurationCurveFiniteSubschemeFiberMap graded f n c hc b) := by
  let D := projectiveConfigurationCurveFiniteSubscheme graded f n c hc
  let e := projectiveConfigurationCurveFiniteSubschemeIso graded f n c hc
  let z := projectiveLineEndpoint K b
  haveI he : IsIso e.hom := by
    dsimp [e]
    infer_instance
  have hm₁ : D.val.subschemeι ≫ pullback.snd f (projectiveLineProjToBase K) ≫ 𝟙 _ =
      e.hom ≫ pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c := by
    simpa [D, e] using
      (projectiveConfigurationCurveFiniteSubschemeIso_hom_toLine graded f n c hc).symm
  change IsIso (pullback.map (D.val.subschemeι ≫ pullback.snd f (projectiveLineProjToBase K)) z
    (pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c) z e.hom (𝟙 _) (𝟙 _) hm₁ (by simp))
  exact @pullback.map_isIso _ _ _ _ _ _ _ _
    (D.val.subschemeι ≫ pullback.snd f (projectiveLineProjToBase K)) z _
    (pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c) z _
    e.hom (𝟙 _) (𝟙 _) hm₁ (by simp)
    he (by infer_instance) (by infer_instance)

/-- The actual fibers of the finite-subscheme family are canonically the
fibers of the pulled-back incidence family. -/
noncomputable def projectiveConfigurationCurveFiniteSubschemeFiberIso
    [IsSeparated f]
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    (rationalCycleFamily_of_finiteSubschemeDatum f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc)).fiber b ≅
      (rationalCycleFamily_of_configurationCurve graded f n c hc).fiber b := by
  letI : IsIso (projectiveConfigurationCurveFiniteSubschemeFiberMap graded f n c hc b) :=
    projectiveConfigurationCurveFiniteSubschemeFiberMap_isIso graded f n c hc b
  exact asIso (projectiveConfigurationCurveFiniteSubschemeFiberMap graded f n c hc b)

/-- The fiber isomorphism commutes with the maps to the fixed projective
scheme. -/
theorem projectiveConfigurationCurveFiniteSubschemeFiberIso_hom_toProjective
    [IsSeparated f]
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    (projectiveConfigurationCurveFiniteSubschemeFiberIso graded f n c hc b).hom ≫
      (rationalCycleFamily_of_configurationCurve graded f n c hc).fiberToScheme b =
      (rationalCycleFamily_of_finiteSubschemeDatum f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc)).fiberToScheme b := by
  let D := projectiveConfigurationCurveFiniteSubscheme graded f n c hc
  let e := projectiveConfigurationCurveFiniteSubschemeIso graded f n c hc
  let z := projectiveLineEndpoint K b
  letI : IsIso (projectiveConfigurationCurveFiniteSubschemeFiberMap graded f n c hc b) :=
    projectiveConfigurationCurveFiniteSubschemeFiberMap_isIso graded f n c hc b
  change projectiveConfigurationCurveFiniteSubschemeFiberMap graded f n c hc b ≫
    (rationalCycleFamily_of_configurationCurve graded f n c hc).fiberToScheme b =
    (rationalCycleFamily_of_finiteSubschemeDatum f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc)).fiberToScheme b
  dsimp [projectiveConfigurationCurveFiniteSubschemeFiberMap,
    PfaffianDescent.RationalCycleFamily.fiberToScheme,
    rationalCycleFamily_of_configurationCurve,
    rationalCycleFamily_of_finiteSubschemeDatum]
  rw [pullback.lift_fst_assoc]
  simpa [D, e] using congrArg
    (pullback.fst (D.val.subschemeι ≫ pullback.snd f (projectiveLineProjToBase K)) z ≫ ·)
    (projectiveConfigurationCurveFiniteSubschemeIso_hom_toProjective graded f n c hc)

/-- The fiber isomorphism also commutes with the structure maps to the
projective line. -/
theorem projectiveConfigurationCurveFiniteSubschemeFiberIso_hom_toLine
    [IsSeparated f]
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    (projectiveConfigurationCurveFiniteSubschemeFiberIso graded f n c hc b).hom ≫
      pullback.snd (rationalCycleFamily_of_configurationCurve graded f n c hc).toLine
        (projectiveLineEndpoint K b) =
      pullback.snd
        (rationalCycleFamily_of_finiteSubschemeDatum f n
          (projectiveConfigurationCurveFiniteSubscheme graded f n c hc)).toLine
        (projectiveLineEndpoint K b) := by
  letI : IsIso (projectiveConfigurationCurveFiniteSubschemeFiberMap graded f n c hc b) :=
    projectiveConfigurationCurveFiniteSubschemeFiberMap_isIso graded f n c hc b
  change projectiveConfigurationCurveFiniteSubschemeFiberMap graded f n c hc b ≫
    pullback.snd (rationalCycleFamily_of_configurationCurve graded f n c hc).toLine
      (projectiveLineEndpoint K b) =
    pullback.snd
      (rationalCycleFamily_of_finiteSubschemeDatum f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc)).toLine
      (projectiveLineEndpoint K b)
  dsimp [projectiveConfigurationCurveFiniteSubschemeFiberMap,
    rationalCycleFamily_of_configurationCurve,
    rationalCycleFamily_of_finiteSubschemeDatum]
  rw [pullback.lift_snd]
  simp

/-- The actual finite-subscheme family and the configuration family have the
same endpoint cycles, including scheme-theoretic multiplicities. -/
theorem rationalCycleFamily_of_projectiveConfigurationCurveFiniteSubscheme_fiberCycle_eq
    [IsSeparated f]
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    (rationalCycleFamily_of_finiteSubschemeDatum f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc)).fiberCycle b =
      (rationalCycleFamily_of_configurationCurve graded f n c hc).fiberCycle b := by
  let F := rationalCycleFamily_of_finiteSubschemeDatum f n
    (projectiveConfigurationCurveFiniteSubscheme graded f n c hc)
  let G := rationalCycleFamily_of_configurationCurve graded f n c hc
  let e := projectiveConfigurationCurveFiniteSubschemeFiberIso graded f n c hc b
  let gbase := pullback.snd G.toLine (projectiveLineEndpoint K b)
  have hmap : e.hom ≫ G.fiberToScheme b = F.fiberToScheme b := by
    simpa [F, G, e] using
      projectiveConfigurationCurveFiniteSubschemeFiberIso_hom_toProjective graded f n c hc b
  have hbase : e.hom ≫ gbase = pullback.snd F.toLine (projectiveLineEndpoint K b) := by
    simpa [F, G, e, gbase] using
      projectiveConfigurationCurveFiniteSubschemeFiberIso_hom_toLine graded f n c hc b
  have h := PfaffianDescent.fiberCycle_eq_pushforward_of_iso f F b e
    (G.fiberToScheme b) gbase hmap hbase
  simpa [F, G, gbase, PfaffianDescent.RationalCycleFamily.fiberCycle] using h

/-- The ideal-defined transport of a configuration curve is a literal
finite-subscheme pencil, with endpoint data obtained by ideal base change. -/
noncomputable def projectiveConfigurationCurveFiniteSubschemePencil
    [IsSeparated f]
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K) :
    FiniteSubschemeDatumPencil f n
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) false)
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) true) :=
  FiniteSubschemeDatumPencil.ofDatum f n
    (projectiveConfigurationCurveFiniteSubscheme graded f n c hc)

/-- A configuration curve whose endpoint incidence schemes are identified
with chosen finite data gives a pencil with precisely those endpoint data.
This is the form needed to use a configuration-space curve as one of
Voisin's residual pencils. -/
noncomputable def projectiveConfigurationCurveFiniteSubschemePencil_retarget
    [IsSeparated f]
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (zeroDatum infinityDatum : FiniteSubschemeDatum f n)
    (zeroIso : (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) false).val.subscheme ≅
        zeroDatum.val.subscheme)
    (zero_over : zeroIso.hom ≫ zeroDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) false).val.subschemeι)
    (infinityIso : (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) true).val.subscheme ≅
        infinityDatum.val.subscheme)
    (infinity_over : infinityIso.hom ≫ infinityDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) true).val.subschemeι) :
    FiniteSubschemeDatumPencil f n zeroDatum infinityDatum :=
  FiniteSubschemeDatumPencil.retarget f
    (projectiveConfigurationCurveFiniteSubschemePencil graded f n c hc)
    zeroDatum infinityDatum zeroIso zero_over infinityIso infinity_over

/-- Retargeting the two endpoint names does not alter the finite étale
family over the parameter line. -/
theorem etale_projectiveConfigurationCurveFiniteSubschemePencil_retarget_toLine
    [IsSeparated f]
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (zeroDatum infinityDatum : FiniteSubschemeDatum f n)
    (zeroIso : (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) false).val.subscheme ≅
        zeroDatum.val.subscheme)
    (zero_over : zeroIso.hom ≫ zeroDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) false).val.subschemeι)
    (infinityIso : (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) true).val.subscheme ≅
        infinityDatum.val.subscheme)
    (infinity_over : infinityIso.hom ≫ infinityDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) true).val.subschemeι) :
    Etale
      ((projectiveConfigurationCurveFiniteSubschemePencil_retarget graded f n c hc
        zeroDatum infinityDatum zeroIso zero_over infinityIso infinity_over).datum.val.subschemeι ≫
        pullback.snd f (projectiveLineProjToBase K)) := by
  change Etale ((projectiveConfigurationCurveFiniteSubscheme graded f n c hc).val.subschemeι ≫
    pullback.snd f (projectiveLineProjToBase K))
  exact etale_projectiveConfigurationCurveFiniteSubscheme_toLine graded f n c hc

/-- This literal pencil has the same endpoint cycles as the configuration
curve from which it was transported. -/
theorem projectiveConfigurationCurveFiniteSubschemePencil_fiberCycle_eq
    [IsSeparated f]
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    (FiniteSubschemeDatumPencil.toRationalCycleFamily f
      (projectiveConfigurationCurveFiniteSubschemePencil graded f n c hc)).fiberCycle b =
      (rationalCycleFamily_of_configurationCurve graded f n c hc).fiberCycle b := by
  change (rationalCycleFamily_of_finiteSubschemeDatum f n
    (projectiveConfigurationCurveFiniteSubscheme graded f n c hc)).fiberCycle b = _
  exact rationalCycleFamily_of_projectiveConfigurationCurveFiniteSubscheme_fiberCycle_eq
    graded f n c hc b

/-- Regard a field-valued unordered configuration as a constant curve over
the projective line.  This is the curve-level form needed to feed a non-split
closed point into a finite-subscheme pencil. -/
noncomputable def projectiveConfigurationConstantCurve
    (n : ℕ)
    (c : Spec (.of K) ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme) :
    projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme :=
  projectiveLineProjToBase K ≫ c

/-- The constant configuration curve lies over the projective-line base. -/
lemma projectiveConfigurationConstantCurve_toBase
    (n : ℕ)
    (c : Spec (.of K) ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _) :
    projectiveConfigurationConstantCurve graded f n c ≫
        projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K := by
  simp [projectiveConfigurationConstantCurve, Category.assoc, hc]

/-- Both marked endpoints of the constant curve are the original
configuration point. -/
lemma projectiveLineEndpoint_comp_projectiveConfigurationConstantCurve
    (n : ℕ)
    (c : Spec (.of K) ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (b : Bool) :
    projectiveLineEndpoint K b ≫
        projectiveConfigurationConstantCurve graded f n c = c := by
  change (projectiveLineEndpoint K b ≫ projectiveLineProjToBase K) ≫ c = c
  rw [projectiveLineEndpoint_toBase, Category.id_comp]

/-- Each endpoint datum of the finite-subscheme pencil attached to a
constant configuration curve has the cycle represented by that configuration.
The statement applies to non-split configurations, so it is compatible with
the degree-ten closed point supplied by Coray. -/
theorem finiteSubschemeDatumAtLineEndpoint_constantConfigurationCurve_cycle
    (n : ℕ)
    (c : Spec (.of K) ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _)
    (b : Bool) :
    finiteSubschemeDatumCycle f
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n
          (projectiveConfigurationConstantCurve graded f n c)
          (projectiveConfigurationConstantCurve_toBase graded f n c hc)) b) =
      projectiveConfigurationCycle graded f n c hc := by
  let d := projectiveConfigurationCurveFiniteSubscheme graded f n
    (projectiveConfigurationConstantCurve graded f n c)
    (projectiveConfigurationConstantCurve_toBase graded f n c hc)
  let curve := projectiveConfigurationConstantCurve graded f n c
  let hcurve := projectiveConfigurationConstantCurve_toBase graded f n c hc
  calc
    finiteSubschemeDatumCycle f (finiteSubschemeDatumAtLineEndpoint f n d b) =
        (rationalCycleFamily_of_finiteSubschemeDatum f n d).fiberCycle b := by
          symm
          exact rationalCycleFamily_of_finiteSubschemeDatum_fiberCycle_eq_endpointDatumCycle
            f n d b
    _ = (rationalCycleFamily_of_configurationCurve graded f n curve hcurve).fiberCycle b := by
          exact rationalCycleFamily_of_projectiveConfigurationCurveFiniteSubscheme_fiberCycle_eq
            graded f n curve hcurve b
    _ = projectiveConfigurationCycle graded f n
        (projectiveLineEndpoint K b ≫ curve) (by
          rw [Category.assoc, hcurve, projectiveLineEndpoint_toBase]) := by
          exact rationalCycleFamily_of_configurationCurve_fiberCycle_eq_projectiveConfigurationCycle
            graded f n curve hcurve b
    _ = projectiveConfigurationCycle graded f n c hc := by
          exact projectiveConfigurationCycle_congr graded f n
            (projectiveLineEndpoint K b ≫ curve) c _ hc
            (projectiveLineEndpoint_comp_projectiveConfigurationConstantCurve
              graded f n c b)

/-- The endpoint identifications of a retargeted configuration pencil
transport finite étaleness to both named endpoint data. -/
theorem etale_projectiveConfigurationCurveFiniteSubschemePencil_retarget_endpoints_toBase
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (zeroDatum infinityDatum : FiniteSubschemeDatum f n)
    (zeroIso : (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) false).val.subscheme ≅
        zeroDatum.val.subscheme)
    (zero_over : zeroIso.hom ≫ zeroDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) false).val.subschemeι)
    (infinityIso : (finiteSubschemeDatumAtLineEndpoint f n
      (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) true).val.subscheme ≅
        infinityDatum.val.subscheme)
    (infinity_over : infinityIso.hom ≫ infinityDatum.val.subschemeι =
      (finiteSubschemeDatumAtLineEndpoint f n
        (projectiveConfigurationCurveFiniteSubscheme graded f n c hc) true).val.subschemeι) :
    Etale (zeroDatum.val.subschemeι ≫ f) ∧
      Etale (infinityDatum.val.subschemeι ≫ f) := by
  constructor
  · exact etale_projectiveConfigurationCurveFiniteSubschemeAtLineEndpoint_of_iso_over
      graded f n c hc false zeroDatum zeroIso zero_over
  · exact etale_projectiveConfigurationCurveFiniteSubschemeAtLineEndpoint_of_iso_over
      graded f n c hc true infinityDatum infinityIso infinity_over

end HomogeneousProjective
