from pathlib import Path
import argparse,json,hashlib,tarfile,gzip
here=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description="Rebuild this source/evidence archive from its original repository-relative files, without running any proof or test.")
parser.add_argument("--repo",required=True,type=Path)
parser.add_argument("--output",type=Path)
parser.add_argument("--verify",action="store_true",help="Rebuild into a streaming hash sink and compare the recorded archive hash")
a=parser.parse_args();repo=a.repo.resolve();inventory=json.loads((here/"archive-files.json").read_text())
class HashSink:
 def __init__(self):self.h=hashlib.sha256();self.bytes=0
 def write(self,data):self.h.update(data);self.bytes+=len(data);return len(data)
 def flush(self):pass
sink=HashSink() if a.verify else (a.output or here/inventory["archive"]).open("wb")
try:
 with gzip.GzipFile(filename="",mode="wb",compresslevel=6,mtime=0,fileobj=sink) as gz:
  with tarfile.open(fileobj=gz,mode="w|",format=tarfile.PAX_FORMAT) as tf:
   for item in inventory["files"]:
    rel=Path(item["original_path"]);assert not rel.is_absolute() and ".." not in rel.parts
    path=repo/rel;assert path.is_file() and not path.is_symlink()
    h=hashlib.sha256()
    with path.open("rb") as f:
     for chunk in iter(lambda:f.read(1048576),b""):h.update(chunk)
    assert path.stat().st_size==item["bytes"] and h.hexdigest()==item["sha256"],str(rel)
    info=tarfile.TarInfo(rel.as_posix());info.size=item["bytes"];info.mode=0o644;info.uid=info.gid=0;info.uname=info.gname="";info.mtime=0;info.pax_headers={}
    with path.open("rb") as f:tf.addfile(info,f)
 if a.verify:
  expected=json.loads((here/"supplement-manifest.json").read_text())["archive"]
  assert sink.h.hexdigest()==expected["sha256"] and sink.bytes==expected["bytes"]
  print(json.dumps({"reproducible_archive_verified":True,"sha256":sink.h.hexdigest(),"bytes":sink.bytes}))
finally:
 if not a.verify:sink.close()
