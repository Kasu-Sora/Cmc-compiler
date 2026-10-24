from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parent
s=(R/'baseline/cmc_concrete_patch_calls.c').read_text();h=(R/'baseline/cmc_concrete_patch_calls.h').read_text()
f=next(x for x in json.loads((R/'metrics/source-functions.json').read_text()) if x['name']=='cmc_patch_resolved_calls')
ls=s.splitlines();body='\n'.join(ls[i-1]for a,b in f['specification']for i in range(a,b+1));header='\n'.join(re.findall(r'\[\[cst::(?:param|require|ensure)\(.*?\)\]\]',h,re.S))
assert re.sub(r'\s+','',body)==re.sub(r'\s+','',header)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(R/'metrics/source-header-contract.json').write_text(json.dumps(dict(status='passed',function='cmc_patch_resolved_calls',normalized_header_body_contract_identical=True,body_contract_sha256=sha(body),header_contract_sha256=sha(header),private_function='cmc_patch_code_arrays has only its BODY contract'),indent=2)+'\n')
