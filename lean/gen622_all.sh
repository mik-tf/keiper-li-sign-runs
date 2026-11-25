#!/bin/bash
# B3: generate all 622 chunk modules C00..C18 (same layout as 711). Run from this directory.
set -e
python3 -I gen622.py --cert KeiperComb/Numerics622Cert.lean
python3 -I gen622.py --chunk 0 1 200 KeiperComb/Numerics622C00.lean
python3 -I gen622.py --chunk 1 200 400 KeiperComb/Numerics622C01.lean
for ci in $(seq 2 17); do
  k0=$((400 + 100*(ci-2))); k1=$((k0+100)); [ $ci -eq 17 ] && k1=1999
  python3 -I gen622.py --chunk $ci $k0 $k1 KeiperComb/Numerics622C$(printf %02d $ci).lean
done
python3 -I gen622.py --chunk 18 1999 2000 KeiperComb/Numerics622C18.lean
