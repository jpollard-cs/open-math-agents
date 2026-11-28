from scipy.optimize import Bounds,LinearConstraint,milp
from scipy.sparse import coo_matrix
import numpy as np
from exact_example import instance
weights,edges=instance(3,12)
radii=sorted(weights); ids={v:i for i,v in enumerate(radii)}
rr=[]; cols=[]; limits=[]
for i,edge in enumerate(sorted(edges)):
    limits.append(len(edge)-1)
    for v in edge: rr.append(i);cols.append(ids[v])
mat=coo_matrix((np.ones(len(rr)),(rr,cols)),shape=(len(limits),len(radii))).tocsc()
sol=milp(-np.array([weights[v] for v in radii],dtype=float),integrality=np.ones(len(radii)),bounds=Bounds(0,1),constraints=LinearConstraint(mat,-np.inf,limits),options={'mip_rel_gap':0.0,'time_limit':90})
print(sol.message, 'objective',-sol.fun,'gap',sol.mip_gap,flush=True)
assert sol.success and abs(sol.fun+2458977)<1e-5
