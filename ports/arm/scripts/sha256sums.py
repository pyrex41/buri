# Regenerate ports/arm/SHA256SUMS over every stored file: sha256sums.py ports/arm
# (packages bytes only; decides nothing).
import hashlib, os, sys
root = sys.argv[1]
paths = []
for d, _, fs in os.walk(root):
    for f in fs:
        p = './' + os.path.relpath(os.path.join(d, f), root)
        if p != './SHA256SUMS':
            paths.append(p)
with open(os.path.join(root, 'SHA256SUMS'), 'w') as out:
    for p in sorted(paths):
        h = hashlib.sha256(open(os.path.join(root, p), 'rb').read()).hexdigest()
        out.write(f'{h}  {p}\n')
print(len(paths))
