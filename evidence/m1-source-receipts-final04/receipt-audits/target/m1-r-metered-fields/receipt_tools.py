import re

def mask_code(s):
    out=list(s);i=0;line=False;block=0;string=False
    while i<len(s):
        c=s[i];n=s[i:i+2]
        if line:
            if c=='\n':line=False
            else:out[i]=' '
        elif block:
            out[i]=' '
            if n=='/*':out[i+1]=' ';block+=1;i+=1
            elif n=='*/':out[i+1]=' ';block-=1;i+=1
        elif string:
            if c!='\n':out[i]=' '
            if c=='\\' and i+1<len(s):out[i+1]=' ';i+=1
            elif c=='"':string=False
        elif n=='//':out[i]=out[i+1]=' ';line=True;i+=1
        elif n=='/*':out[i]=out[i+1]=' ';block=1;i+=1
        elif c=='"':out[i]=' ';string=True
        i+=1
    return ''.join(out)

def close(s,start,op='(',cl=')'):
    m=mask_code(s);d=0
    for i in range(start,len(s)):
        if m[i]==op:d+=1
        elif m[i]==cl:
            d-=1
            if d==0:return i
    raise ValueError('unbalanced')

def fnparts(s,name):
    p=re.search(r'(?m)^(?:pub\(crate\) )?fn '+re.escape(name)+r'\(',s)
    if not p:raise ValueError(name)
    a=p.start();opening=s.index('\n{\n',a)+1;z=close(s,opening,'{','}')+1
    return a,opening,z,s[a:opening],s[opening+1:z-1]

def header_pair(h,cost):
    m=re.search(r'-> \(r: (.*?)\)\n',h,re.S);assert m,h[:120]
    t=m.group(1);h=h[:m.start()]+f'-> (r: ({t}, Ghost<nat>))\n'+h[m.end():]
    e=h.index('    ensures');pre=h[:e];ens=h[e+len('    ensures'):];ens=re.sub(r'\br\b','r.0',ens)
    return pre+'    ensures\n        '+cost+',\n'+ens,t

def wrap_returns(body,count):
    m=mask_code(body);edits=[]
    for k in re.finditer(r'\breturn\b',m):
        a=k.end();i=a;ds=[0,0,0]
        while i<len(body):
            c=m[i]
            if c=='(':ds[0]+=1
            elif c==')':ds[0]-=1
            elif c=='[':ds[1]+=1
            elif c==']':ds[1]-=1
            elif c=='{':ds[2]+=1
            elif c=='}':ds[2]-=1
            elif c in ';,' and ds==[0,0,0]:break
            i+=1
        expr=body[a:i].strip();edits.append((a,i,' ('+expr+', Ghost('+count+'))'))
    for a,z,x in reversed(edits):body=body[:a]+x+body[z:]
    return body

def wrap_tail(body,count,marker=None):
    if marker is None:
        matches=list(re.finditer(r'(?m)^    Ok\(',body));assert matches,body[-200:];a=matches[-1].start()
    else:a=body.rindex('\n    '+marker)+1
    tail=body[a:].strip();return body[:a]+'    let ordinary_result = {\n        '+tail+'\n    };\n    (ordinary_result, Ghost('+count+'))\n'

def adapt_calls(s,names):
    m=mask_code(s);edits=[]
    for k in re.finditer(r'\b('+'|'.join(map(re.escape,sorted(names,key=len,reverse=True)))+r')\s*\(',m):
        if re.search(r'\bfn\s*$',m[max(0,k.start()-20):k.start()]):continue
        p=m.index('(',k.start());z=close(s,p)+1
        if s[z:z+2]=='.0':continue
        edits.append(z)
    for z in reversed(edits):s=s[:z]+'.0'+s[z:]
    return s

def wire_child(body,name,counter):
    m=mask_code(body);edits=[]
    for k in re.finditer(r'\b'+re.escape(name)+r'\s*\(',m):
        p=m.index('(',k.start());z=close(body,p)+1
        assert body[z:z+2]=='.0',(name,body[k.start():z+20])
        call=body[k.start():z]
        expr='{ let (r_child_result, Ghost(r_child_units)) = '+call+'; proof { '+counter+' = '+counter+' + r_child_units; } r_child_result }'
        edits.append((k.start(),z+2,expr))
    for a,z,x in reversed(edits):body=body[:a]+x+body[z:]
    return body,len(edits)

def wire_question_child(body,name,counter):
    m=mask_code(body);edits=[]
    for k in re.finditer(r'\b'+re.escape(name)+r'\s*\(',m):
        p=m.index('(',k.start());z=close(body,p)+1
        assert body[z:z+3]=='.0?',(name,body[k.start():z+16])
        call=body[k.start():z]
        expr='{ let (r_child_result, Ghost(r_child_units)) = '+call+'; proof { '+counter+' = '+counter+' + r_child_units; } match r_child_result { Ok(value) => value, Err(error) => return (Err(error), Ghost('+counter+')) } }'
        edits.append((k.start(),z+3,expr))
    for a,z,x in reversed(edits):body=body[:a]+x+body[z:]
    return body,len(edits)
