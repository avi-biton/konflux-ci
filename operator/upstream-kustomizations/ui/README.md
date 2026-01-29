# UI

## Overview

This component will deploy the UI.

`proxy` - Forwards requests to the kube api, and redirects the user to perform
authentication if the user doesn't have a valid cookie.

## Dependencies

`Dex` is required to be present for `oauth2-proxy` to be deployed.

## Certificate Infrastructure

### Architecture

The UI component uses a certificate trust chain to enable secure TLS communication between oauth2-proxy and Dex:

```
self-signed-cluster-issuer (ClusterIssuer)
    └── dex-cert (Certificate, isCA: true)
            └── dex-ca-issuer (Issuer)
                    └── oauth2-proxy-ca-cert (Certificate)
```

### Components

1. **dex-cert** (`certmanager/certificate.yaml`)
   - Self-signed certificate with `isCA: true`
   - Issued by `self-signed-cluster-issuer`
   - Used by Dex pod for TLS serving
   - Acts as Certificate Authority for oauth2-proxy client certificates

2. **dex-ca-issuer** (`certmanager/certificate.yaml`)
   - Namespace-scoped Issuer in `konflux-ui`
   - Uses `dex-cert` secret as its CA source
   - Issues certificates that share Dex's CA for mutual trust

3. **oauth2-proxy-ca-cert** (`certmanager/certificate.yaml`)
   - Client certificate issued by `dex-ca-issuer`
   - Contains the same CA bundle as `dex-cert`
   - Only the `ca.crt` field is used by oauth2-proxy

4. **serving-cert** (`certmanager/certificate.yaml`)
   - Separate certificate for nginx/proxy TLS serving
   - Not related to Dex trust chain

### Resource Creation Order

The order doesn't strictly matter because:
- cert-manager automatically retries if dependencies aren't ready
- Kubernetes will wait for secrets to become available before starting pods

**Typical Creation Flow:**
1. `dex-cert` created → cert-manager issues it
2. `dex-ca-issuer` created → waits for `dex-cert` secret
3. `oauth2-proxy-ca-cert` created → waits for `dex-ca-issuer` to be ready
4. `proxy` deployment created → waits for `oauth2-proxy-ca-cert` secret

### Certificate Rotation and Renewal

**Automatic Renewal:**
- cert-manager automatically renews certificates before expiry
- Default renewal: 2/3 through certificate lifetime (e.g., 60 days for 90-day cert)
- When `dex-cert` renews, cert-manager automatically re-issues `oauth2-proxy-ca-cert`

**Impact on Running Pods:**
- Dex pod: Automatically picks up new certificate on next TLS handshake
- oauth2-proxy pod: Go applications re-read `SSL_CERT_FILE` on each connection
- **No pod restart required** for CA certificate updates

### TLS Configuration

oauth2-proxy uses the `SSL_CERT_FILE` environment variable to trust Dex:

```yaml
env:
- name: SSL_CERT_FILE
  value: /etc/ssl/certs/oauth2-proxy-ca.crt

volumeMounts:
- name: oauth2-proxy-ca
  mountPath: /etc/ssl/certs/oauth2-proxy-ca.crt
  subPath: ca.crt
  readOnly: true

volumes:
- name: oauth2-proxy-ca
  secret:
    secretName: oauth2-proxy-ca-cert
    items:
    - key: ca.crt
      path: ca.crt
```

### Security Model

**Credential Isolation:**
- `dex-cert` secret contains Dex's TLS certificate and private key
- Only the Dex pod mounts the full `dex-cert` secret
- oauth2-proxy pod only mounts `ca.crt` from `oauth2-proxy-ca-cert`
- oauth2-proxy pod **cannot** access `dex-cert` secret (Kubernetes RBAC isolation)

### Troubleshooting

**Verify Certificate Trust Chain:**
```bash
# Check all certificates are ready
kubectl get certificates -n konflux-ui

# Verify issuer is ready
kubectl get issuer dex-ca-issuer -n konflux-ui

# Compare CA certificates (should be identical)
kubectl get secret dex-cert -n konflux-ui -o jsonpath='{.data.ca\.crt}' | base64 -d | openssl x509 -text -noout | head -20
kubectl get secret oauth2-proxy-ca-cert -n konflux-ui -o jsonpath='{.data.ca\.crt}' | base64 -d | openssl x509 -text -noout | head -20
```

**Check oauth2-proxy TLS Configuration:**
```bash
# Verify SSL_CERT_FILE is set
kubectl get deployment proxy -n konflux-ui -o jsonpath='{.spec.template.spec.containers[?(@.name=="oauth2-proxy")].env[?(@.name=="SSL_CERT_FILE")]}'

# Verify CA certificate is mounted
kubectl get deployment proxy -n konflux-ui -o jsonpath='{.spec.template.spec.containers[?(@.name=="oauth2-proxy")].volumeMounts[?(@.name=="oauth2-proxy-ca")]}'

# Check oauth2-proxy logs for TLS errors
kubectl logs -n konflux-ui -l app=proxy -c oauth2-proxy | grep -i "tls\|certificate\|x509"
```

**Common Issues:**

1. **Certificate Not Ready**
   - Symptom: Pod stuck in `ContainerCreating`
   - Check: `kubectl describe certificate oauth2-proxy-ca-cert -n konflux-ui`
   - Solution: Wait for cert-manager to issue the certificate

2. **TLS Verification Failure**
   - Symptom: oauth2-proxy logs show "x509: certificate signed by unknown authority"
   - Check: Verify CA certificates match (see commands above)
   - Solution: Delete and recreate `oauth2-proxy-ca-cert` to refresh CA bundle

3. **Issuer Not Ready**
   - Symptom: `oauth2-proxy-ca-cert` shows "Issuer not ready"
   - Check: `kubectl describe issuer dex-ca-issuer -n konflux-ui`
   - Solution: Verify `dex-cert` secret exists and contains valid CA
