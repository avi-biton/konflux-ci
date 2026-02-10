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

package clusterinfo

import (
	"context"
	"errors"
	"testing"

	"github.com/onsi/gomega"
	configv1 "github.com/openshift/api/config/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apimachinery/pkg/version"
	"sigs.k8s.io/controller-runtime/pkg/client"
	"sigs.k8s.io/controller-runtime/pkg/client/fake"
)

// mockDiscoveryClient implements DiscoveryClient for testing.
type mockDiscoveryClient struct {
	resources      map[string]*metav1.APIResourceList
	resourceErrors map[string]error
	serverVersion  *version.Info
	versionErr     error
}

func (m *mockDiscoveryClient) ServerResourcesForGroupVersion(groupVersion string) (*metav1.APIResourceList, error) {
	// Check for specific errors first
	if m.resourceErrors != nil {
		if err, ok := m.resourceErrors[groupVersion]; ok {
			return nil, err
		}
	}
	if r, ok := m.resources[groupVersion]; ok {
		return r, nil
	}
	// Return a NotFound error by default (simulates missing API group)
	return nil, apierrors.NewNotFound(schema.GroupResource{Group: groupVersion}, "")
}

func (m *mockDiscoveryClient) ServerVersion() (*version.Info, error) {
	if m.versionErr != nil {
		return nil, m.versionErr
	}
	return m.serverVersion, nil
}

func TestDetectWithClient_OpenShift(t *testing.T) {
	g := gomega.NewWithT(t)

	mock := &mockDiscoveryClient{
		resources: map[string]*metav1.APIResourceList{
			"config.openshift.io/v1": {
				APIResources: []metav1.APIResource{
					{Kind: "ClusterVersion"},
					{Kind: "Infrastructure"},
				},
			},
		},
		serverVersion: &version.Info{
			GitVersion: "v1.29.4",
			Major:      "1",
			Minor:      "29",
		},
	}

	// Create fake client with ClusterVersion resource
	scheme := runtime.NewScheme()
	_ = configv1.Install(scheme)
	fakeClient := fake.NewClientBuilder().WithScheme(scheme).Build()

	info, err := DetectWithClient(mock, fakeClient)
	g.Expect(err).NotTo(gomega.HaveOccurred())
	g.Expect(info.Platform()).To(gomega.Equal(OpenShift))
	g.Expect(info.IsOpenShift()).To(gomega.BeTrue())
}

func TestDetectWithClient_Default(t *testing.T) {
	g := gomega.NewWithT(t)

	mock := &mockDiscoveryClient{
		resources: map[string]*metav1.APIResourceList{
			// No OpenShift resources
		},
		serverVersion: &version.Info{
			GitVersion: "v1.30.0",
			Major:      "1",
			Minor:      "30",
		},
	}

	info, err := DetectWithClient(mock, nil)
	g.Expect(err).NotTo(gomega.HaveOccurred())
	g.Expect(info.Platform()).To(gomega.Equal(Default))
	g.Expect(info.IsOpenShift()).To(gomega.BeFalse())
}

func TestDetectWithClient_OpenShiftGroupWithoutClusterVersion(t *testing.T) {
	g := gomega.NewWithT(t)

	mock := &mockDiscoveryClient{
		resources: map[string]*metav1.APIResourceList{
			"config.openshift.io/v1": {
				APIResources: []metav1.APIResource{
					{Kind: "Infrastructure"},
					// No ClusterVersion
				},
			},
		},
		serverVersion: &version.Info{GitVersion: "v1.29.0"},
	}

	info, err := DetectWithClient(mock, nil)
	g.Expect(err).NotTo(gomega.HaveOccurred())
	g.Expect(info.Platform()).To(gomega.Equal(Default), "should return Default when ClusterVersion is missing")
}

func TestDetectWithClient_ServerVersionError(t *testing.T) {
	g := gomega.NewWithT(t)

	mock := &mockDiscoveryClient{
		resources:  map[string]*metav1.APIResourceList{},
		versionErr: errors.New("connection refused"),
	}

	info, err := DetectWithClient(mock, nil)
	g.Expect(err).NotTo(gomega.HaveOccurred())
	_, err = info.K8sVersion()
	g.Expect(err).To(gomega.HaveOccurred())
}

func TestDetectWithClient_PlatformDetectionError(t *testing.T) {
	g := gomega.NewWithT(t)

	// Simulate a non-NotFound error (e.g., network failure, unauthorized)
	mock := &mockDiscoveryClient{
		resources: map[string]*metav1.APIResourceList{},
		resourceErrors: map[string]error{
			"config.openshift.io/v1": apierrors.NewServiceUnavailable("API server unavailable"),
		},
		serverVersion: &version.Info{GitVersion: "v1.29.0"},
	}

	_, err := DetectWithClient(mock, nil)
	g.Expect(err).To(gomega.HaveOccurred())
	g.Expect(err.Error()).To(gomega.ContainSubstring("failed to detect platform"))
}

func TestInfo_K8sVersion(t *testing.T) {
	g := gomega.NewWithT(t)

	expectedVersion := &version.Info{
		GitVersion: "v1.29.4",
		Major:      "1",
		Minor:      "29",
		Platform:   "linux/amd64",
	}

	mock := &mockDiscoveryClient{
		resources:     map[string]*metav1.APIResourceList{},
		serverVersion: expectedVersion,
	}

	info, err := DetectWithClient(mock, nil)
	g.Expect(err).NotTo(gomega.HaveOccurred())
	v, err := info.K8sVersion()
	g.Expect(err).NotTo(gomega.HaveOccurred())
	g.Expect(v).NotTo(gomega.BeNil())
	g.Expect(v.GitVersion).To(gomega.Equal(expectedVersion.GitVersion))
	g.Expect(v.Major).To(gomega.Equal(expectedVersion.Major))
	g.Expect(v.Minor).To(gomega.Equal(expectedVersion.Minor))
}

func TestInfo_HasResource(t *testing.T) {
	tests := []struct {
		name         string
		resources    map[string]*metav1.APIResourceList
		groupVersion string
		kind         string
		expected     bool
	}{
		{
			name: "resource exists",
			resources: map[string]*metav1.APIResourceList{
				"apps/v1": {
					APIResources: []metav1.APIResource{
						{Kind: "Deployment"},
						{Kind: "StatefulSet"},
					},
				},
			},
			groupVersion: "apps/v1",
			kind:         "Deployment",
			expected:     true,
		},
		{
			name: "resource does not exist in group",
			resources: map[string]*metav1.APIResourceList{
				"apps/v1": {
					APIResources: []metav1.APIResource{
						{Kind: "Deployment"},
					},
				},
			},
			groupVersion: "apps/v1",
			kind:         "DaemonSet",
			expected:     false,
		},
		{
			name:         "group does not exist",
			resources:    map[string]*metav1.APIResourceList{},
			groupVersion: "nonexistent.io/v1",
			kind:         "SomeResource",
			expected:     false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			g := gomega.NewWithT(t)

			mock := &mockDiscoveryClient{
				resources:     tt.resources,
				serverVersion: &version.Info{GitVersion: "v1.29.0"},
			}

			info, err := DetectWithClient(mock, nil)
			g.Expect(err).NotTo(gomega.HaveOccurred())

			result, err := info.HasResource(tt.groupVersion, tt.kind)
			g.Expect(err).NotTo(gomega.HaveOccurred())
			g.Expect(result).To(gomega.Equal(tt.expected))
		})
	}
}

func TestInfo_HasTekton(t *testing.T) {
	tests := []struct {
		name      string
		resources map[string]*metav1.APIResourceList
		expected  bool
	}{
		{
			name: "Tekton installed",
			resources: map[string]*metav1.APIResourceList{
				"tekton.dev/v1": {
					APIResources: []metav1.APIResource{
						{Kind: "Pipeline"},
						{Kind: "Task"},
						{Kind: "PipelineRun"},
					},
				},
			},
			expected: true,
		},
		{
			name:      "Tekton not installed",
			resources: map[string]*metav1.APIResourceList{},
			expected:  false,
		},
		{
			name: "Tekton group exists but no Pipeline",
			resources: map[string]*metav1.APIResourceList{
				"tekton.dev/v1": {
					APIResources: []metav1.APIResource{
						{Kind: "Task"},
					},
				},
			},
			expected: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			g := gomega.NewWithT(t)

			mock := &mockDiscoveryClient{
				resources:     tt.resources,
				serverVersion: &version.Info{GitVersion: "v1.29.0"},
			}

			info, err := DetectWithClient(mock, nil)
			g.Expect(err).NotTo(gomega.HaveOccurred())

			result, err := info.HasTekton()
			g.Expect(err).NotTo(gomega.HaveOccurred())
			g.Expect(result).To(gomega.Equal(tt.expected))
		})
	}
}

func TestInfo_HasAllResources(t *testing.T) {
	tests := []struct {
		name           string
		resources      map[string]*metav1.APIResourceList
		resourceErrors map[string]error
		groupVersion   string
		kinds          []string
		expectedResult bool
		expectErr      bool
	}{
		{
			name: "all kinds present",
			resources: map[string]*metav1.APIResourceList{
				"example.com/v1": {
					APIResources: []metav1.APIResource{
						{Kind: "Foo"},
						{Kind: "Bar"},
					},
				},
			},
			groupVersion:   "example.com/v1",
			kinds:          []string{"Foo", "Bar"},
			expectedResult: true,
		},
		{
			name: "one kind missing",
			resources: map[string]*metav1.APIResourceList{
				"example.com/v1": {
					APIResources: []metav1.APIResource{
						{Kind: "Foo"},
					},
				},
			},
			groupVersion:   "example.com/v1",
			kinds:          []string{"Foo", "Bar"},
			expectedResult: false,
		},
		{
			name: "empty kinds returns true",
			resources: map[string]*metav1.APIResourceList{
				"example.com/v1": {APIResources: []metav1.APIResource{}},
			},
			groupVersion:   "example.com/v1",
			kinds:          []string{},
			expectedResult: true,
		},
		{
			name:           "NotFound returns false without error",
			resources:      map[string]*metav1.APIResourceList{},
			groupVersion:   "missing.io/v1",
			kinds:          []string{"Something"},
			expectedResult: false,
		},
		{
			name:      "non-NotFound error is propagated",
			resources: map[string]*metav1.APIResourceList{},
			resourceErrors: map[string]error{
				"example.com/v1": apierrors.NewForbidden(
					schema.GroupResource{Group: "example.com"}, "", errors.New("RBAC")),
			},
			groupVersion:   "example.com/v1",
			kinds:          []string{"Foo"},
			expectedResult: false,
			expectErr:      true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			g := gomega.NewWithT(t)

			mock := &mockDiscoveryClient{
				resources:      tt.resources,
				resourceErrors: tt.resourceErrors,
				serverVersion:  &version.Info{GitVersion: "v1.29.0"},
			}
			info, err := DetectWithClient(mock, nil)
			g.Expect(err).NotTo(gomega.HaveOccurred())

			result, err := info.HasAllResources(tt.groupVersion, tt.kinds)

			if tt.expectErr {
				g.Expect(err).To(gomega.HaveOccurred())
				g.Expect(result).To(gomega.BeFalse())
				return
			}
			g.Expect(err).NotTo(gomega.HaveOccurred())
			g.Expect(result).To(gomega.Equal(tt.expectedResult))
		})
	}
}

func TestInfo_HasCertManager(t *testing.T) {
	tests := []struct {
		name             string
		setupClusterInfo func() *Info
		expectedResult   bool
	}{
		{
			name: "cert-manager installed - all resources exist",
			setupClusterInfo: func() *Info {
				mockClient := &mockDiscoveryClient{
					resources: map[string]*metav1.APIResourceList{
						"cert-manager.io/v1": {
							GroupVersion: "cert-manager.io/v1",
							APIResources: []metav1.APIResource{
								{Kind: "Certificate"},
								{Kind: "Issuer"},
								{Kind: "ClusterIssuer"},
							},
						},
					},
					serverVersion: &version.Info{GitVersion: "v1.30.0"},
				}
				info, _ := DetectWithClient(mockClient, nil)
				return info
			},
			expectedResult: true,
		},
		{
			name: "cert-manager not installed - only Certificate exists",
			setupClusterInfo: func() *Info {
				mockClient := &mockDiscoveryClient{
					resources: map[string]*metav1.APIResourceList{
						"cert-manager.io/v1": {
							GroupVersion: "cert-manager.io/v1",
							APIResources: []metav1.APIResource{
								{Kind: "Certificate"},
							},
						},
					},
					serverVersion: &version.Info{GitVersion: "v1.30.0"},
				}
				info, _ := DetectWithClient(mockClient, nil)
				return info
			},
			expectedResult: false,
		},
		{
			name: "cert-manager not installed - only Issuer exists",
			setupClusterInfo: func() *Info {
				mockClient := &mockDiscoveryClient{
					resources: map[string]*metav1.APIResourceList{
						"cert-manager.io/v1": {
							GroupVersion: "cert-manager.io/v1",
							APIResources: []metav1.APIResource{
								{Kind: "Issuer"},
							},
						},
					},
					serverVersion: &version.Info{GitVersion: "v1.30.0"},
				}
				info, _ := DetectWithClient(mockClient, nil)
				return info
			},
			expectedResult: false,
		},
		{
			name: "cert-manager not installed - only ClusterIssuer exists",
			setupClusterInfo: func() *Info {
				mockClient := &mockDiscoveryClient{
					resources: map[string]*metav1.APIResourceList{
						"cert-manager.io/v1": {
							GroupVersion: "cert-manager.io/v1",
							APIResources: []metav1.APIResource{
								{Kind: "ClusterIssuer"},
							},
						},
					},
					serverVersion: &version.Info{GitVersion: "v1.30.0"},
				}
				info, _ := DetectWithClient(mockClient, nil)
				return info
			},
			expectedResult: false,
		},
		{
			name: "cert-manager not installed - two resources exist but one missing",
			setupClusterInfo: func() *Info {
				mockClient := &mockDiscoveryClient{
					resources: map[string]*metav1.APIResourceList{
						"cert-manager.io/v1": {
							GroupVersion: "cert-manager.io/v1",
							APIResources: []metav1.APIResource{
								{Kind: "Certificate"},
								{Kind: "Issuer"},
								// ClusterIssuer is missing
							},
						},
					},
					serverVersion: &version.Info{GitVersion: "v1.30.0"},
				}
				info, _ := DetectWithClient(mockClient, nil)
				return info
			},
			expectedResult: false,
		},
		{
			name: "cert-manager not installed - no resources exist",
			setupClusterInfo: func() *Info {
				mockClient := &mockDiscoveryClient{
					resources:     map[string]*metav1.APIResourceList{},
					serverVersion: &version.Info{GitVersion: "v1.30.0"},
				}
				info, _ := DetectWithClient(mockClient, nil)
				return info
			},
			expectedResult: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			g := gomega.NewWithT(t)

			clusterInfo := tt.setupClusterInfo()
			result, err := clusterInfo.HasCertManager()

			g.Expect(err).NotTo(gomega.HaveOccurred())
			g.Expect(result).To(gomega.Equal(tt.expectedResult))
		})
	}
}

func TestPlatform_IsOpenShift(t *testing.T) {
	tests := []struct {
		platform Platform
		expected bool
	}{
		{OpenShift, true},
		{Default, false},
		{Platform("unknown"), false},
	}

	for _, tt := range tests {
		t.Run(string(tt.platform), func(t *testing.T) {
			g := gomega.NewWithT(t)
			g.Expect(tt.platform.IsOpenShift()).To(gomega.Equal(tt.expected))
		})
	}
}

func TestInfo_OpenShiftVersion(t *testing.T) {
	tests := []struct {
		name            string
		platform        Platform
		clusterVersion  *configv1.ClusterVersion
		expectedVersion string
		expectError     bool
	}{
		{
			name:     "OpenShift with valid ClusterVersion",
			platform: OpenShift,
			clusterVersion: &configv1.ClusterVersion{
				ObjectMeta: metav1.ObjectMeta{Name: "version"},
				Status: configv1.ClusterVersionStatus{
					Desired: configv1.Release{
						Version: "4.15.3",
					},
				},
			},
			expectedVersion: "4.15.3",
			expectError:     false,
		},
		{
			name:            "OpenShift without ClusterVersion resource",
			platform:        OpenShift,
			clusterVersion:  nil,
			expectedVersion: UnknownVersion,
			expectError:     false,
		},
		{
			name:     "OpenShift with empty version field",
			platform: OpenShift,
			clusterVersion: &configv1.ClusterVersion{
				ObjectMeta: metav1.ObjectMeta{Name: "version"},
				Status: configv1.ClusterVersionStatus{
					Desired: configv1.Release{
						Version: "",
					},
				},
			},
			expectedVersion: UnknownVersion,
			expectError:     false,
		},
		{
			name:            "Non-OpenShift platform",
			platform:        Default,
			clusterVersion:  nil,
			expectedVersion: "",
			expectError:     false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			g := gomega.NewWithT(t)

			// Create scheme and fake client
			scheme := runtime.NewScheme()
			_ = configv1.Install(scheme)

			var fakeClient client.Client
			if tt.clusterVersion != nil {
				fakeClient = fake.NewClientBuilder().
					WithScheme(scheme).
					WithObjects(tt.clusterVersion).
					Build()
			} else {
				fakeClient = fake.NewClientBuilder().
					WithScheme(scheme).
					Build()
			}

			// Create mock discovery client
			mockDiscovery := &mockDiscoveryClient{
				resources:     map[string]*metav1.APIResourceList{},
				serverVersion: &version.Info{GitVersion: "v1.29.0"},
			}

			if tt.platform == OpenShift {
				mockDiscovery.resources["config.openshift.io/v1"] = &metav1.APIResourceList{
					APIResources: []metav1.APIResource{
						{Kind: "ClusterVersion"},
					},
				}
			}

			info, err := DetectWithClient(mockDiscovery, fakeClient)
			g.Expect(err).NotTo(gomega.HaveOccurred())
			g.Expect(info.Platform()).To(gomega.Equal(tt.platform))

			versionStr, err := info.OpenShiftVersion(context.Background())

			if tt.expectError {
				g.Expect(err).To(gomega.HaveOccurred())
			} else {
				g.Expect(err).NotTo(gomega.HaveOccurred())
				g.Expect(versionStr).To(gomega.Equal(tt.expectedVersion))
			}
		})
	}
}

func TestInfo_OpenShiftVersion_NoRuntimeClient(t *testing.T) {
	g := gomega.NewWithT(t)

	// Create OpenShift platform detection
	mockDiscovery := &mockDiscoveryClient{
		resources: map[string]*metav1.APIResourceList{
			"config.openshift.io/v1": {
				APIResources: []metav1.APIResource{
					{Kind: "ClusterVersion"},
				},
			},
		},
		serverVersion: &version.Info{GitVersion: "v1.29.0"},
	}

	// Pass nil as runtime client
	info, err := DetectWithClient(mockDiscovery, nil)
	g.Expect(err).NotTo(gomega.HaveOccurred())
	g.Expect(info.IsOpenShift()).To(gomega.BeTrue())

	// Should return UnknownVersion when runtime client is nil
	versionStr, err := info.OpenShiftVersion(context.Background())
	g.Expect(err).NotTo(gomega.HaveOccurred())
	g.Expect(versionStr).To(gomega.Equal(UnknownVersion))
}
