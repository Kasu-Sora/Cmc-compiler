"""Read-only region extraction used for migration cost and contract audits."""
import re

def mask_c(text):
    return re.sub(r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'', lambda m: re.sub(r'[^\n]', ' ', m.group()),text,flags=re.S)

def c_functions(text):
    masked=mask_c(text); result=[]
    for m in re.finditer(r'^(?:static )?(?:int|long long|void)\s+(\w+)\s*\(',masked,re.M):
        at=m.end()+re.search(r'[{};]',masked[m.end():]).start()
        end=at+1
        if masked[at]=='{':
            depth=1
            while depth:
                depth+=(masked[end]=='{')-(masked[end]=='}');end+=1
        result.append(dict(name=m.group(1),start=m.start(),body_start=at,end=end,prototype=masked[at]==';'))
    return result

def coq_mask(text, mask_strings=True):
    # Nested comments and doubled quotes in Rocq strings. Preserve positions.
    out=list(text);i=0;depth=0;string=False
    while i<len(text):
        hide=True
        if depth:
            if text[i:i+2]=='(*': depth+=1;n=2
            elif text[i:i+2]=='*)':depth-=1;n=2
            else:n=1
        elif string:
            hide=mask_strings
            if text[i:i+2]=='""':n=2
            elif text[i]=='"':string=False;n=1
            else:n=1
        elif text[i:i+2]=='(*':depth=1;n=2
        elif text[i]=='"':string=True;n=1;hide=mask_strings
        else:i+=1;continue
        for j in range(i,i+n):
            if hide and text[j]!='\n':out[j]=' '
        i+=n
    assert depth==0 and not string
    return ''.join(out)

def coq_commands(text):
    masked=coq_mask(text);pos=0;out=[]
    for m in re.finditer(r'\.(?=\s|$)',masked):
        start=pos
        while start<m.end() and masked[start].isspace():start+=1
        if start<m.end():out.append((start,m.end(),masked[start:m.end()]))
        pos=m.end()
    assert not masked[pos:].strip(),masked[pos:]
    return out

def coq_regions(text):
    out=[];pending=None
    for a,b,cmd in coq_commands(text):
        head=re.match(r'(?:(?:Local|Global|Program)\s+)?(\w+)(?:\s+(\w+))?',cmd)
        kind,name=head.groups() if head else ('other',None)
        if pending:
            if kind in ['Qed','Defined','Admitted','Abort']:
                pending.update(end=b,body_end=a,ending=kind);out.append(pending);pending=None
            elif kind=='Proof':pending['body_start']=b
        elif kind in ['Lemma','Theorem','Corollary','Fact','Remark','Proposition']:
            pending=dict(kind=kind,name=name,start=a,statement_end=b)
        else:out.append(dict(kind=kind,name=name,start=a,end=b))
    assert pending is None,pending
    return out

def line_span(text,a,b):return [text[:a].count('\n')+1,text[:b-1].count('\n')+1]
def nonblank(text,a,b):return sum(bool(l.strip()) for l in text[a:b].splitlines())
