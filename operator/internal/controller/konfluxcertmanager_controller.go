/*
Copyright 2025 Konflux CI.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

package controller

import (
	"context"
	"fmt"

	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/runtime"
	ctrl "sigs.k8s.io/controller-runtime"
	"sigs.k8s.io/controller-runtime/pkg/builder"
	"sigs.k8s.io/controller-runtime/pkg/client"
	logf "sigs.k8s.io/controller-runtime/pkg/log"

	konfluxv1alpha1 "github.com/konflux-ci/konflux-ci/operator/api/v1alpha1"
	"github.com/konflux-ci/konflux-ci/operator/pkg/manifests"
)

const (
	// CertManagerConditionTypeReady is the condition type for overall readiness
	CertManagerConditionTypeReady = "Ready"
	// FieldManagerCertManager is the field manager name for cert-manager resources
	FieldManagerCertManager = "konflux-cert-manager-controller"
)

// KonfluxCertManagerReconciler reconciles a KonfluxCertManager object
type KonfluxCertManagerReconciler struct {
	client.Client
	Scheme      *runtime.Scheme
	ObjectStore *manifests.ObjectStore
}

// +kubebuilder:rbac:groups=konflux.konflux-ci.dev,resources=konfluxcertmanagers,verbs=get;list;watch;create;update;patch;delete
// +kubebuilder:rbac:groups=konflux.konflux-ci.dev,resources=konfluxcertmanagers/status,verbs=get;update;patch
// +kubebuilder:rbac:groups=konflux.konflux-ci.dev,resources=konfluxcertmanagers/finalizers,verbs=update
// +kubebuilder:rbac:groups=cert-manager.io,resources=clusterissuers,verbs=get;list;watch;create;patch
// +kubebuilder:rbac:groups=cert-manager.io,resources=certificates,verbs=get;list;watch;create;patch

// Reconcile is part of the main kubernetes reconciliation loop which aims to
// move the current state of the cluster closer to the desired state.
func (r *KonfluxCertManagerReconciler) Reconcile(ctx context.Context, req ctrl.Request) (ctrl.Result, error) {
	log := logf.FromContext(ctx)

	// Fetch the KonfluxCertManager instance
	certManager := &konfluxv1alpha1.KonfluxCertManager{}
	if err := r.Get(ctx, req.NamespacedName, certManager); err != nil {
		return ctrl.Result{}, client.IgnoreNotFound(err)
	}

	log.Info("Reconciling KonfluxCertManager", "name", certManager.Name)

	// Apply manifests only if createClusterIssuer is enabled (defaults to true)
	if certManager.Spec.ShouldCreateClusterIssuer() {
		if err := r.applyManifests(ctx, certManager); err != nil {
			log.Error(err, "Failed to apply manifests")
			SetFailedCondition(certManager, CertManagerConditionTypeReady, "ApplyFailed", err)
			if updateErr := r.Status().Update(ctx, certManager); updateErr != nil {
				log.Error(updateErr, "Failed to update status")
			}
			return ctrl.Result{}, err
		}
	} else {
		log.Info("Skipping manifest application - createClusterIssuer is false")
	}

	// Check the status of owned deployments and update KonfluxCertManager status
	// Note: cert-manager has no deployments, so this will set Ready=true with appropriate message
	if err := UpdateComponentStatuses(ctx, r.Client, certManager, CertManagerConditionTypeReady); err != nil {
		log.Error(err, "Failed to update component statuses")
		SetFailedCondition(certManager, CertManagerConditionTypeReady, "FailedToGetDeploymentStatus", err)
		if updateErr := r.Status().Update(ctx, certManager); updateErr != nil {
			log.Error(updateErr, "Failed to update status")
		}
		return ctrl.Result{}, err
	}

	log.Info("Successfully reconciled KonfluxCertManager")
	return ctrl.Result{}, nil
}

// applyManifests loads and applies all embedded manifests to the cluster.
// Manifests are parsed once and cached; deep copies are used during reconciliation.
func (r *KonfluxCertManagerReconciler) applyManifests(ctx context.Context, owner *konfluxv1alpha1.KonfluxCertManager) error {
	log := logf.FromContext(ctx)

	objects, err := r.ObjectStore.GetForComponent(manifests.CertManager)
	if err != nil {
		return fmt.Errorf("failed to get parsed manifests for CertManager: %w", err)
	}

	for _, obj := range objects {
		// Set ownership labels and owner reference
		if err := setOwnership(obj, owner, string(manifests.CertManager), r.Scheme); err != nil {
			return fmt.Errorf("failed to set ownership for %s/%s (%s) from %s: %w",
				obj.GetNamespace(), obj.GetName(), getKind(obj), manifests.CertManager, err)
		}

		if err := applyObject(ctx, r.Client, obj, FieldManagerCertManager); err != nil {
			gvk := obj.GetObjectKind().GroupVersionKind()
			if gvk.Group == CertManagerGroup || gvk.Group == KyvernoGroup {
				// TODO: Remove this once we decide how to install cert-manager crds in envtest
				// TODO: Remove this once we decide if we want to have a dependency on Kyverno
				log.Info("Skipping resource: CRD not installed",
					"kind", gvk.Kind,
					"apiVersion", gvk.GroupVersion().String(),
					"namespace", obj.GetNamespace(),
					"name", obj.GetName(),
				)
				continue
			}
			return fmt.Errorf("failed to apply object %s/%s (%s) from %s: %w",
				obj.GetNamespace(), obj.GetName(), getKind(obj), manifests.CertManager, err)
		}
	}
	return nil
}

// SetupWithManager sets up the controller with the Manager.
func (r *KonfluxCertManagerReconciler) SetupWithManager(mgr ctrl.Manager) error {
	return ctrl.NewControllerManagedBy(mgr).
		For(&konfluxv1alpha1.KonfluxCertManager{}).
		Named("konfluxcertmanager").
		// Watch for changes to cert-manager resources
		Owns(&corev1.Secret{}, builder.WithPredicates(labelsOrAnnotationsChangedPredicate)).
		Complete(r)
}
