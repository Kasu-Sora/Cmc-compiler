import re
token=re.compile(r'\s*(==|&&|\|\||::|\+\+|--|[A-Za-z_][A-Za-z_0-9]*|[0-9]+i?|[][();+*<~=-])')
prec={'||':10,'&&':20,'==':30,'<':30,'::':40,'++':40,'+':50,'-':50,'*':60}
class Parser:
 def __init__(self,s):
  self.ts=[];i=0
  while s[i:].strip():
   m=token.match(s,i)
   if not m:raise ValueError(s[i:i+100])
   self.ts.append(m[1]);i=m.end()
  self.ts.append('EOF');self.i=0
 def pop(self,t=None):
  x=self.ts[self.i];self.i+=1
  if t is not None:assert x==t,(x,t,self.ts[self.i-5:self.i+5])
  return x
 def peek(self):return self.ts[self.i]
 def expr(self,limit=0):
  t=self.pop()
  if t=='(':
   a=self.expr();self.pop(')')
  elif t=='[':
   xs=[]
   if self.peek()!=']':
    xs.append(self.expr())
    while self.peek()==';':self.pop();xs.append(self.expr())
   self.pop(']');a=('list',xs)
  elif t=='if':
   cond=self.expr();self.pop('then');yes=self.expr();self.pop('else');no=self.expr();a=('if',cond,yes,no)
  elif t in ('~','--'):a=('unary',t,self.expr(70))
  else:
   assert t not in ('EOF','then','else',')'),t
   a=('id',t)
  while True:
   t=self.peek()
   if t in prec:
    p=prec[t]
    if p<limit:break
    self.pop();b=self.expr(p if t in ('::','++') else p+1);a=('bin',t,a,b)
   elif t not in ('EOF','then','else',')',']',';') and t not in prec:
    if 80<limit:break
    a=('app',a,self.expr(81))
   else:break
  return a
 def all(self):
  x=self.expr();self.pop('EOF');return x
source_params={'cm_binding_array','cm_member_array','cm_call_ok','cm_local_slot_ok','cm_ann_enter_call','cm_init_tail_code','cm_return_tail_code'}
policy_params={'cm_binding_address_code','cm_emit_prologue','cm_stmt_code_count','cm_temp_store_code','cm_temp_load_code','cm_rvalue_code_count','cm_binary_finish_code','cm_assign_tail_code','cm_index_tail_code','cm_arg_final_code','cm_emit_args_reload','cm_function_pc'}
ann_params={'cm_ann_pop','cm_ann_replace','cm_ann_leave_call'}
names={'left':'lhs','right':'rhs','ilength':'Zlength','TL':'tl','REVERSE':'rev','SUC':'S','T':'true','F':'false'}
def flat(a):
 args=[]
 while a[0]=='app':args.insert(0,a[2]);a=a[1]
 return a,args

def emit(a,pattern=False):
 k=a[0]
 if k=='id':
  s=names.get(a[1],a[1]);return re.sub(r'^(\d+)i$',r'\1',s)
 if k=='list':return '['+'; '.join(emit(x,pattern) for x in a[1])+']'
 if k=='if':return '(if '+emit(a[1])+' then '+emit(a[2])+' else '+emit(a[3])+')'
 if k=='unary':return '('+{'~':'negb ','--':'- '}[a[1]]+emit(a[2])+')'
 if k=='bin':
  op,l,r=a[1:]
  if op=='==' and r==('list',[]):return '(cm_list_empty '+emit(l)+')'
  return '('+emit(l)+' '+{'==':'=?','<':'<?'}.get(op,op)+' '+emit(r)+')'
 if k=='app':
  f,args=flat(a);assert f[0]=='id',a
  name=f[1];extra=[]
  if not pattern:
   if name in source_params:extra=['sp']
   if name in policy_params:extra=['(cm_source_function_policy sp)']
   if name in ann_params:extra=['ap']
   if name=='HD':
    hdtype=flat(args[0])[0][1]
    default={'cm_ann_cursors':'cm_cursor_nil','cm_ann_saved':'cm_saved_nil','cm_ann_calls':'cm_call_nil'}[hdtype]
    name='hd';extra=['('+default+' ap)']
  return '('+' '.join([names.get(name,name)]+extra+[emit(x,pattern) for x in args])+')'
 raise ValueError(a)
def striptypes(s):
 # Only simple variable/list binders, including the env function type.
 return re.sub(r'\((\w+|\[\]):(?:\([^()]+\)list|[A-Za-z_][\w]*(?:->[A-Za-z_][\w]*)*)\)',r'\1',s)
def clauses(s):
 result=[];depth=0;start=0;i=0
 while i<len(s):
  if s[i]=='(':depth+=1
  if s[i]==')':depth-=1
  if depth==0 and s[i:i+2]=='&&':result.append(s[start:i].strip());start=i+2;i+=1
  i+=1
 result.append(s[start:].strip());return result
