/* ----------------------------------------------------------------------
   SPARTA - Stochastic PArallel Rarefied-gas Time-accurate Analyzer
   http://sparta.sandia.gov
   Steve Plimpton, sjplimp@gmail.com, Michael Gallis, magalli@sandia.gov
   Sandia National Laboratories

   Copyright (2014) Sandia Corporation.  Under the terms of Contract
   DE-AC04-94AL85000 with Sandia Corporation, the U.S. Government retains
   certain rights in this software.  This software is distributed under
   the GNU General Public License.

   See the README file in the top-level SPARTA directory.
------------------------------------------------------------------------- */

#include "ctype.h"
#include "surf.h"
#include "style_surf_collide.h"
#include "style_surf_react.h"
#include "surf_collide.h"
#include "surf_react.h"
#include "domain.h"
#include "region.h"
#include "grid.h"
#include "comm.h"
#include "geometry.h"
#include "input.h"
#include "math_extra.h"
#include "math_const.h"
#include "hash3.h"
#include "memory.h"
#include "error.h"
// for implicit
#include "fix_ablate.h"
#include "modify.h"
#include "cut2d.h"

using namespace SPARTA_NS;
using namespace MathConst;

enum{TALLYAUTO,TALLYREDUCE,TALLYRVOUS};         // same as Update
enum{REGION_ALL,REGION_ONE,REGION_CENTER};      // same as Grid
enum{TYPE,MOLECULE,ID};
enum{LT,LE,GT,GE,EQ,NEQ,BETWEEN};
enum{INT,DOUBLE};                      // several files

#define DELTA 1024
#define DELTAMODEL 4
#define EPSSQ 1.0e-12
#define EPSILON_GRID 1.0e-3
#define EPSSURF 1.0e-4
#define BIG 1.0e20
#define MAXGROUP 32

/* ---------------------------------------------------------------------- */

Surf::Surf(SPARTA *sparta) : Pointers(sparta)
{
  me = comm->me;
  nprocs = comm->nprocs;

  exist = 0;
  implicit = 0;
  distributed = 0;
  surf_collision_check = 1;

  gnames = (char **) memory->smalloc(MAXGROUP*sizeof(char *),"surf:gnames");
  bitmask = (int *) memory->smalloc(MAXGROUP*sizeof(int),"surf:bitmask");
  inversemask = (int *) memory->smalloc(MAXGROUP*sizeof(int),
                                        "surf:inversemask");

  for (int i = 0; i < MAXGROUP; i++) bitmask[i] = 1 << i;
  for (int i = 0; i < MAXGROUP; i++) inversemask[i] = bitmask[i] ^ ~0;

  ngroup = 1;
  int n = strlen("all") + 1;
  gnames[0] = new char[n];
  strcpy(gnames[0],"all");

  nsurf = 0;

  nlocal = nghost = nmax = 0;
  lines = NULL;
  tris = NULL;

  nown = maxown = 0;
  mylines = NULL;
  mytris = NULL;

  nsc = maxsc = 0;
  sc = NULL;
  nsr = maxsr = 0;
  sr = NULL;

  tally_comm = TALLYAUTO;

  // custom per-surf vectors/arrays

  ncustom = 0;
  ename = NULL;
  etype = esize = ewhich = NULL;

  ncustom_ivec = ncustom_iarray = 0;
  icustom_ivec = icustom_iarray = NULL;
  eivec = NULL;
  eiarray = NULL;
  eicol = NULL;

  ncustom_dvec = ncustom_darray = 0;
  icustom_dvec = icustom_darray = NULL;
  edvec = NULL;
  edarray = NULL;
  edcol = NULL;

  custom_restart_flag = NULL;

  // allocate hash for surf IDs

  hash = new MySurfHash();
  hashfilled = 0;

  // for implicit surface
  aveFlag = 0;
}

/* ---------------------------------------------------------------------- */

Surf::~Surf()
{
  for (int i = 0; i < ngroup; i++) delete [] gnames[i];
  memory->sfree(gnames);
  memory->sfree(bitmask);
  memory->sfree(inversemask);

  memory->sfree(lines);
  memory->sfree(tris);
  memory->sfree(mylines);
  memory->sfree(mytris);

  for (int i = 0; i < nsc; i++) delete sc[i];
  memory->sfree(sc);
  for (int i = 0; i < nsr; i++) delete sr[i];
  memory->sfree(sr);

  hash->clear();
  delete hash;

  for (int i = 0; i < ncustom; i++) delete [] ename[i];
  memory->sfree(ename);
  memory->destroy(etype);
  memory->destroy(esize);
  memory->destroy(ewhich);

  for (int i = 0; i < ncustom_ivec; i++) memory->destroy(eivec[i]);
  for (int i = 0; i < ncustom_iarray; i++) memory->destroy(eiarray[i]);
  for (int i = 0; i < ncustom_dvec; i++) memory->destroy(edvec[i]);
  for (int i = 0; i < ncustom_darray; i++) memory->destroy(edarray[i]);

  memory->destroy(icustom_ivec);
  memory->destroy(icustom_iarray);
  memory->sfree(eivec);
  memory->sfree(eiarray);
  memory->destroy(eicol);
  memory->destroy(icustom_dvec);
  memory->destroy(icustom_darray);
  memory->sfree(edvec);
  memory->sfree(edarray);
  memory->destroy(edcol);
}

/* ---------------------------------------------------------------------- */

void Surf::global(char *arg)
{
  if (exist)
    error->all(FLERR,"Cannot set global surfs when surfaces already exist");

  if (strcmp(arg,"explicit") == 0) {
    implicit = 0;
    distributed = 0;
  } else if (strcmp(arg,"explicit/distributed") == 0) {
    implicit = 0;
    distributed = 1;
  } else if (strcmp(arg,"implicit") == 0) {
    implicit = 1;
    distributed = 1;
  } else error->all(FLERR,"Illegal global command");
}

/* ---------------------------------------------------------------------- */

void Surf::modify_params(int narg, char **arg)
{
  if (narg < 2) error->all(FLERR,"Illegal surf_modify command");
  int igroup = find_group(arg[0]);
  if (igroup < 0) error->all(FLERR,"Surf_modify surface group is not defined");
  int groupbit = bitmask[igroup];

  int dim = domain->dimension;

  int iarg = 1;
  while (iarg < narg) {
    if (strcmp(arg[iarg],"collide") == 0) {
      if (iarg+2 > narg) error->all(FLERR,"Illegal surf_modify command");
      if (!exist) error->all(FLERR,"Surf_modify when surfs do not yet exist");

      int isc = find_collide(arg[iarg+1]);
      if (isc < 0) error->all(FLERR,"Could not find surf_modify sc-ID");

      // NOTE: is this also needed for mylines and mytris?
      // set surf collision model for each surf in surface group

      if (dim == 2) {
        for (int i = 0; i < nlocal+nghost; i++)
          if (lines[i].mask & groupbit) lines[i].isc = isc;
      }
      if (dim == 3) {
        for (int i = 0; i < nlocal+nghost; i++)
          if (tris[i].mask & groupbit) tris[i].isc = isc;
      }

      iarg += 2;

    } else if (strcmp(arg[iarg],"react") == 0) {
      if (iarg+2 > narg) error->all(FLERR,"Illegal surf_modify command");
      if (!exist) error->all(FLERR,"Surf_modify when surfs do not yet exist");

      int isr;
      if (strcmp(arg[iarg+1],"none") == 0) isr = -1;
      else {
        isr = find_react(arg[iarg+1]);
        if (isr < 0) error->all(FLERR,"Could not find surf_modify sr-ID");
      }

      // set surf reaction model for each surf in surface group

      if (dim == 2) {
        for (int i = 0; i < nlocal+nghost; i++)
          if (lines[i].mask & groupbit) lines[i].isr = isr;
      }
      if (dim == 3) {
        for (int i = 0; i < nlocal+nghost; i++)
          if (tris[i].mask & groupbit) tris[i].isr = isr;
      }

      iarg += 2;

    } else if (strcmp(arg[iarg],"implicit") == 0) {
      if (iarg+6 > narg) error->all(FLERR,"Illegal surf_modify command");
      if (!exist) error->all(FLERR,"Surf_modify when surfs do not yet exist");

      int impflag;
      if (strcmp(arg[iarg+1],"yes") == 0) impflag = 1;
      else if (strcmp(arg[iarg+1],"no") == 0) impflag = 0;
      else error->all(FLERR,"Illegal collide_modify command");

      thresh = input->numeric(FLERR,arg[iarg+2]);
      if (thresh < 0 || thresh > 255)
        error->all(FLERR,"Read_surf thresh must be bounded as (0,255)");

      // find ablate fix
      char *ablateID = arg[iarg+3];
      int ifix = modify->find_fix(ablateID);
      if (ifix < 0)
        error->all(FLERR,"Fix ID for read_surf does not exist");
      if (strcmp(modify->fix[ifix]->style,"ablate") != 0)
        error->all(FLERR,"Fix for read_surf is not a fix ablate");
      ablate = (FixAblate *) modify->fix[ifix];
      ggroup = grid->find_group(arg[iarg+4]);
      if (ggroup != ablate->igroup)
        error->all(FLERR,"Read_surf group does not match fix ablate group");

      // temporary
      if (strcmp(arg[iarg+5],"inout") == 0) 0; // do nothing
      else if (strcmp(arg[iarg+5],"ave") == 0) aveFlag = 1;
      else error->all(FLERR,"Unknown surface corner setting called");

      // DO NOT SET SURFACE TO IMPLICIT YET or below will give error
      // nxyz already takes into account subcells
      grid->check_uniform_group(ggroup,nxyz,corner,xyzsize);

      // corner points needs one more in each dim
      Nxyz = (nxyz[0]+1)*(nxyz[1]+1);
      if(dim == 3) Nxyz *= (nxyz[2]+1);

      if(impflag) {

        // cvalues is the grid (no overlaps)
        // icvalues is setting each corner for each cell based on cvalues
        // .. icvalues is cvalues in read_isurf and fix_ablate
        memory->create(cvalues,Nxyz,"surf:cvalues");

        if (dim == 2) {
          memory->create(icvalues,grid->nlocal,4,"surf:icvalues");
          for (int i = 0; i < grid->nlocal; i++) {
            for (int j = 0; j < 4; j++)
              icvalues[i][j] = 0.0;
          }
        } else {
          memory->create(icvalues,grid->nlocal,8,"surf:icvalues");
          for (int i = 0; i < grid->nlocal; i++) {
            for (int j = 0; j < 8; j++)
              icvalues[i][j] = 0.0;
          }
        }

        // find all corner values but later only store those within
        // .. ggroup
        set_corners();
        MPI_Barrier(world);

        /*----------------------------------------------------------*/
        // delete old explicit surfaces
        // copied from remove_surf.cpp
        if (comm->me == 0)
          if (screen) fprintf(screen,"Removing explicit surfs ...\n");

        //printf("sort\n");
        if (particle->exist) particle->sort();
        MPI_Barrier(world);

        //printf("remove_2/3d\n");
        if (domain->dimension == 2) {
          remove_2d(groupbit);
          check_watertight_2d();
          if (nsurf == 0) exist = 0 ;
        } else {
          remove_3d(groupbit);
          check_watertight_3d();
          if (nsurf == 0) exist = 0 ;
        }

        //printf("reset grid\n");
        setup_owned();
        grid->unset_neighbors();
        grid->remove_ghosts();

        if (particle->exist && grid->nsplitlocal) {
          Grid::ChildCell *cells = grid->cells;
          int nglocal = grid->nlocal;
          for (int icell = 0; icell < nglocal; icell++)
            if (cells[icell].nsplit > 1)
              grid->combine_split_cell_particles(icell,1);
        }

        grid->clear_surf();
        if (exist) grid->surf2grid(1);
        MPI_Barrier(world);

        if (particle->exist && grid->nsplitlocal) {
          Grid::ChildCell *cells = grid->cells;
          int nglocal = grid->nlocal;
          for (int icell = 0; icell < nglocal; icell++)
            if (cells[icell].nsplit > 1)
              grid->assign_split_cell_particles(icell);
        }
        MPI_Barrier(world);

        grid->setup_owned();
        grid->acquire_ghosts();
        grid->reset_neighbors();
        comm->reset_neighbors();

        grid->set_inout();
        grid->type_check();
        MPI_Barrier(world);

        if (comm->me == 0)
          if (screen) fprintf(screen,"Finished deleting old explicit surfaces\n");
        memory->destroy(cvalues);
        /*----------------------------------------------------------*/        

        // set flag to implicit (always distributed?)
        implicit = 1;
        distributed = 1;

        // all implicit surface generator handled in fix_ablate
        // .. also invokes Marching Squares/Cubes
        exist = 1;
        tvalues = NULL; // do later
        cpushflag = 0; // do later
        char *sgroupID = NULL; // do later

        ablate->store_corners(nxyz[0],nxyz[1],nxyz[2],corner,xyzsize,
                        icvalues,tvalues,thresh,sgroupID,cpushflag);

        if (ablate->nevery == 0) modify->delete_fix(ablateID);
        MPI_Barrier(world);

        // add timing later

      }

      iarg += 6;
      //error->one(FLERR,"implicit check");
    } else error->all(FLERR,"Illegal surf_modify command");
  }
}

/* ---------------------------------------------------------------------- */

void Surf::init()
{
  int dim = domain->dimension;
  bigint flag,allflag;

  // warn if surfs are distributed (explicit or implicit)
  //   and grid->cutoff < 0.0, since each proc will have copy of all cells

  if (exist && distributed && grid->cutoff < 0.0)
    if (comm->me == 0)
      error->warning(FLERR,"Surfs are distributed with infinite grid cutoff");

  // check that surf element types are all values >= 1

  flag = 0;
  if (dim == 2) {
    for (int i = 0; i < nlocal; i++)
      if (lines[i].type <= 0) flag++;
  }
  if (dim == 3) {
    for (int i = 0; i < nlocal; i++)
      if (tris[i].type <= 0) flag++;
  }

  if (distributed)
    MPI_Allreduce(&flag,&allflag,1,MPI_SPARTA_BIGINT,MPI_SUM,world);
  else allflag = flag;

  if (allflag) {
    char str[64];
    sprintf(str,BIGINT_FORMAT
            " surface elements with invalid type <= 0",allflag);
    error->all(FLERR,str);
  }

  // check that every element is assigned to a surf collision model
  // skip if caller turned off the check, e.g. BalanceGrid, b/c too early

  if (surf_collision_check) {
    flag = 0;
    if (dim == 2) {
      for (int i = 0; i < nlocal+nghost; i++)
        if (lines[i].isc < 0) flag++;
    }
    if (dim == 3) {
      for (int i = 0; i < nlocal+nghost; i++)
        if (tris[i].isc < 0) flag++;
    }

    if (distributed)
      MPI_Allreduce(&flag,&allflag,1,MPI_SPARTA_BIGINT,MPI_SUM,world);
    else allflag = flag;

    if (allflag) {
      char str[64];
      sprintf(str,BIGINT_FORMAT
              " surface elements not assigned to a collision model",allflag);
      error->all(FLERR,str);
    }
  }

  // if a surf element is assigned a reaction model
  // must have a collision model that allows reactions

  if (surf_collision_check) {
    flag = 0;
    if (dim == 2) {
      for (int i = 0; i < nlocal+nghost; i++)
        if (lines[i].isr >= 0 && sc[lines[i].isc]->allowreact == 0) flag++;
    }
    if (dim == 3) {
      for (int i = 0; i < nlocal+nghost; i++)
        if (tris[i].isr >= 0 && sc[tris[i].isc]->allowreact == 0) flag++;
    }

    if (distributed)
      MPI_Allreduce(&flag,&allflag,1,MPI_SPARTA_BIGINT,MPI_SUM,world);
    else allflag = flag;

    if (allflag) {
      char str[128];
      sprintf(str,BIGINT_FORMAT " surface elements with reaction model, "
              "but invalid collision model",allflag);
      error->all(FLERR,str);
    }
  }

  // checks on transparent surfaces
  // must be assigned to transparent surf collision model

  if (surf_collision_check) {
    flag = 0;
    if (dim == 2) {
      for (int i = 0; i < nlocal+nghost; i++) {
        if (!lines[i].transparent) continue;
        if (!sc[lines[i].isc]->transparent) flag++;
      }
    }
    if (dim == 3) {
      for (int i = 0; i < nlocal+nghost; i++) {
        if (!tris[i].transparent) continue;
        if (!sc[tris[i].isc]->transparent) flag++;
      }
    }

    if (distributed)
      MPI_Allreduce(&flag,&allflag,1,MPI_SPARTA_BIGINT,MPI_SUM,world);
    else allflag = flag;

    if (allflag) {
      char str[128];
      sprintf(str,BIGINT_FORMAT " transparent surface elements "
              "with invalid collision model or reaction model",allflag);
      error->all(FLERR,str);
    }
  }

  // initialize surf collision and reaction models

  for (int i = 0; i < nsc; i++) sc[i]->init();
  for (int i = 0; i < nsr; i++) sr[i]->init();

  // if first run after reading a restart file,
  // delete any custom surf attributes that have not been re-defined
  // use nactive since remove_custom() may alter ncustom

  if (custom_restart_flag) {
    int nactive = ncustom;
    for (int i = 0; i < nactive; i++)
      if (custom_restart_flag[i] == 0) remove_custom(i);
    delete [] custom_restart_flag;
    custom_restart_flag = NULL;
  }
}

/* ----------------------------------------------------------------------
   remove all surfs
   called by FixAblate
------------------------------------------------------------------------- */

void Surf::clear()
{
  nsurf = 0;
  nlocal = nghost = 0;
  nown = 0;
  hash->clear();
  hashfilled = 0;
}

/* ----------------------------------------------------------------------
   remove ghost surfs
------------------------------------------------------------------------- */

void Surf::remove_ghosts()
{
  nghost = 0;
}

/* ----------------------------------------------------------------------
   add a line to lines list
   called by ReadSurf (for non-distributed surfs) and ReadISurf
------------------------------------------------------------------------- */

void Surf::add_line(surfint id, int itype, double *p1, double *p2)
{
  if (nlocal == nmax) {
    if ((bigint) nmax + DELTA > MAXSMALLINT)
      error->one(FLERR,"Surf add_line overflowed");
    nmax += DELTA;
    grow(nmax-DELTA);
  }

  lines[nlocal].id = id;
  lines[nlocal].type = itype;
  lines[nlocal].mask = 1;
  lines[nlocal].isc = lines[nlocal].isr = -1;
  lines[nlocal].p1[0] = p1[0];
  lines[nlocal].p1[1] = p1[1];
  lines[nlocal].p1[2] = 0.0;
  lines[nlocal].p2[0] = p2[0];
  lines[nlocal].p2[1] = p2[1];
  lines[nlocal].p2[2] = 0.0;
  lines[nlocal].transparent = 0;
  nlocal++;
}

/* ----------------------------------------------------------------------
   add a line to owned or ghost lines list, depending on ownflag
   called by Grid::unpack_one() or Grid::coarsen_cell()
------------------------------------------------------------------------- */

void Surf::add_line_copy(int ownflag, Line *line)
{
  int index;

  if (ownflag) {
    if (nlocal == nmax) {
      if ((bigint) nmax + DELTA > MAXSMALLINT)
        error->one(FLERR,"Surf add_line_copy overflowed");
      nmax += DELTA;
      grow(nmax-DELTA);
    }
    index = nlocal;
    nlocal++;

  } else {
    if (nlocal+nghost == nmax) {
      if ((bigint) nmax + DELTA > MAXSMALLINT)
        error->one(FLERR,"Surf add_line_copy overflowed");
      nmax += DELTA;
      grow(nmax-DELTA);
    }
    index = nlocal+nghost;
    nghost++;
  }

  memcpy(&lines[index],line,sizeof(Line));
}

/* ----------------------------------------------------------------------
   add a line to mylines list
   called by ReadSurf for distributed surfs
   NOT adding one line at a time, rather inserting at location M based on ID
   assume mylines has been pre-allocated to correct length
   caller sets surf->nown
------------------------------------------------------------------------- */

void Surf::add_line_own(surfint id, int itype, double *p1, double *p2)
{
  int m = (id-1) / nprocs;

  mylines[m].id = id;
  mylines[m].type = itype;
  mylines[m].mask = 1;
  mylines[m].isc = mylines[m].isr = -1;
  mylines[m].p1[0] = p1[0];
  mylines[m].p1[1] = p1[1];
  mylines[m].p1[2] = 0.0;
  mylines[m].p2[0] = p2[0];
  mylines[m].p2[1] = p2[1];
  mylines[m].p2[2] = 0.0;
  mylines[m].transparent = 0;
}

/* ----------------------------------------------------------------------
   add a line to tmplines list
   called by ReadSurf for multiple file input
------------------------------------------------------------------------- */

void Surf::add_line_temporary(surfint id, int itype, double *p1, double *p2)
{
  if (ntmp == nmaxtmp) {
    if ((bigint) nmaxtmp + DELTA > MAXSMALLINT)
      error->one(FLERR,"Surf add_line_tmeporary overflowed");
    nmaxtmp += DELTA;
    grow_temporary(nmaxtmp-DELTA);
  }

  tmplines[ntmp].id = id;
  tmplines[ntmp].type = itype;
  tmplines[ntmp].mask = 1;
  tmplines[ntmp].isc = tmplines[ntmp].isr = -1;
  tmplines[ntmp].p1[0] = p1[0];
  tmplines[ntmp].p1[1] = p1[1];
  tmplines[ntmp].p1[2] = 0.0;
  tmplines[ntmp].p2[0] = p2[0];
  tmplines[ntmp].p2[1] = p2[1];
  tmplines[ntmp].p2[2] = 0.0;
  tmplines[ntmp].transparent = 0;
  ntmp++;
}

/* ----------------------------------------------------------------------
   add a triangle to tris list
   called by ReadSurf (for non-distributed surfs) and
     by ReadISurf via FixAblate and Marching Cubes/Squares
------------------------------------------------------------------------- */

void Surf::add_tri(surfint id, int itype, double *p1, double *p2, double *p3)
{
  if (nlocal == nmax) {
    if ((bigint) nmax + DELTA > MAXSMALLINT)
      error->one(FLERR,"Surf add_tri overflowed");
    nmax += DELTA;
    grow(nmax-DELTA);
  }

  tris[nlocal].id = id;
  tris[nlocal].type = itype;
  tris[nlocal].mask = 1;
  tris[nlocal].isc = tris[nlocal].isr = -1;
  tris[nlocal].p1[0] = p1[0];
  tris[nlocal].p1[1] = p1[1];
  tris[nlocal].p1[2] = p1[2];
  tris[nlocal].p2[0] = p2[0];
  tris[nlocal].p2[1] = p2[1];
  tris[nlocal].p2[2] = p2[2];
  tris[nlocal].p3[0] = p3[0];
  tris[nlocal].p3[1] = p3[1];
  tris[nlocal].p3[2] = p3[2];
  tris[nlocal].transparent = 0;
  nlocal++;
}

/* ----------------------------------------------------------------------
   add a triangle to owned or ghost list, depending on ownflag
   called by Grid::unpack_one
------------------------------------------------------------------------- */

void Surf::add_tri_copy(int ownflag, Tri *tri)
{
  int index;

  if (ownflag) {
    if (nlocal == nmax) {
      if ((bigint) nmax + DELTA > MAXSMALLINT)
        error->one(FLERR,"Surf add_tri_copy overflowed");
      nmax += DELTA;
      grow(nmax-DELTA);
    }
    index = nlocal;
    nlocal++;

  } else {
    if (nlocal+nghost == nmax) {
      if ((bigint) nmax + DELTA > MAXSMALLINT)
        error->one(FLERR,"Surf add_tri_copy overflowed");
      nmax += DELTA;
      grow(nmax-DELTA);
    }
    index = nlocal+nghost;
    nghost++;
  }

  memcpy(&tris[index],tri,sizeof(Tri));
}

/* ----------------------------------------------------------------------
   add a triangls's info to mytris list
   called by ReadSurf for distributed surfs
   NOT adding one tri at a time, rather inserting at location M based on ID
   assume mytris has been pre-allocated to correct length
   caller sets surf->nown
------------------------------------------------------------------------- */

void Surf::add_tri_own(surfint id, int itype, double *p1, double *p2, double *p3)
{
  int m = (id-1) / nprocs;

  mytris[m].id = id;
  mytris[m].type = itype;
  mytris[m].mask = 1;
  mytris[m].isc = mytris[m].isr = -1;
  mytris[m].p1[0] = p1[0];
  mytris[m].p1[1] = p1[1];
  mytris[m].p1[2] = p1[2];
  mytris[m].p2[0] = p2[0];
  mytris[m].p2[1] = p2[1];
  mytris[m].p2[2] = p2[2];
  mytris[m].p3[0] = p3[0];
  mytris[m].p3[1] = p3[1];
  mytris[m].p3[2] = p3[2];
  mytris[m].transparent = 0;
}

/* ----------------------------------------------------------------------
   add a triangls's info to mytris list
   called by ReadSurf for distributed surfs when clip3d adds one
   ARE adding one tri at a time, IDs will be renumbered after
     and tris re-distributed to procs
   check if mytris needs to be reallocated
   increment nown
------------------------------------------------------------------------- */

void Surf::add_tri_own_clip(surfint id, int itype,
                            double *p1, double *p2, double *p3)
{
  if (nown == maxown) {
    if ((bigint) maxown + DELTA > MAXSMALLINT)
      error->one(FLERR,"Surf add_tri overflowed");
    maxown += DELTA;
    grow_own(maxown-DELTA);
  }

  mytris[nown].id = id;
  mytris[nown].type = itype;
  mytris[nown].mask = 1;
  mytris[nown].isc = mytris[nown].isr = -1;
  mytris[nown].p1[0] = p1[0];
  mytris[nown].p1[1] = p1[1];
  mytris[nown].p1[2] = p1[2];
  mytris[nown].p2[0] = p2[0];
  mytris[nown].p2[1] = p2[1];
  mytris[nown].p2[2] = p2[2];
  mytris[nown].p3[0] = p3[0];
  mytris[nown].p3[1] = p3[1];
  mytris[nown].p3[2] = p3[2];
  mytris[nown].transparent = 0;
  nown++;
}

/* ----------------------------------------------------------------------
   add a triangle to tmptris list
   called by ReadSurf for mutliple file input
------------------------------------------------------------------------- */

void Surf::add_tri_temporary(surfint id, int itype,
                             double *p1, double *p2, double *p3)
{
  if (ntmp == nmaxtmp) {
    if ((bigint) nmaxtmp + DELTA > MAXSMALLINT)
      error->one(FLERR,"Surf add_tri_temporary overflowed");
    nmaxtmp += DELTA;
    grow_temporary(nmaxtmp-DELTA);
  }

  tmptris[ntmp].id = id;
  tmptris[ntmp].type = itype;
  tmptris[ntmp].mask = 1;
  tmptris[ntmp].isc = tmptris[ntmp].isr = -1;
  tmptris[ntmp].p1[0] = p1[0];
  tmptris[ntmp].p1[1] = p1[1];
  tmptris[ntmp].p1[2] = p1[2];
  tmptris[ntmp].p2[0] = p2[0];
  tmptris[ntmp].p2[1] = p2[1];
  tmptris[ntmp].p2[2] = p2[2];
  tmptris[ntmp].p3[0] = p3[0];
  tmptris[ntmp].p3[1] = p3[1];
  tmptris[ntmp].p3[2] = p3[2];
  tmptris[ntmp].transparent = 0;
  ntmp++;
}

/* ----------------------------------------------------------------------
   hash all my nlocal surfs with key = ID, value = index
   called only for distributed explicit surfs
------------------------------------------------------------------------- */

void Surf::rehash()
{
  if (implicit) return;

  // hash all nlocal surfs
  // key = ID, value = index into lines or tris

  hash->clear();
  hashfilled = 1;

  if (domain->dimension == 2) {
    for (int isurf = 0; isurf < nlocal; isurf++)
      (*hash)[lines[isurf].id] = isurf;
  } else {
    for (int isurf = 0; isurf < nlocal; isurf++)
      (*hash)[tris[isurf].id] = isurf;
  }
}

/* ----------------------------------------------------------------------
   return 1 if all surfs are transparent, else return 0
   called by set_inout()
------------------------------------------------------------------------- */

int Surf::all_transparent()
{
  // implicit surfs cannot be transparent

  if (implicit) return 0;

  // explicit surfs may be transparent

  int flag = 0;
  if (domain->dimension == 2) {
    for (int i = 0; i < nlocal; i++)
      if (!lines[i].transparent) flag = 1;
  }
  if (domain->dimension == 3) {
    for (int i = 0; i < nlocal; i++)
      if (!tris[i].transparent) flag = 1;
  }

  int allflag;
  if (distributed)
    MPI_Allreduce(&flag,&allflag,1,MPI_INT,MPI_SUM,world);
  else allflag = flag;

  if (allflag) return 0;
  return 1;
}

/* ----------------------------------------------------------------------
   count owned surf elements = every Pth surf from global Nsurf list
   only called when surfs = explict (all or distributed)
   nothing to do when distributed b/c mylines/mytris already setup
------------------------------------------------------------------------ */

void Surf::setup_owned()
{
  if (distributed) return;

  nown = nsurf/nprocs;
  if (comm->me < nsurf % nprocs) nown++;
}

/* ----------------------------------------------------------------------
   set bounding box around all surfs based on their pts
   sets surf->bblo and surf->bbhi
   for 2d, set zlo,zhi to box bounds
   only called when surfs = explict (all or distributed)
------------------------------------------------------------------------- */

void Surf::bbox_all()
{
  int i,j;
  double bblo_one[3],bbhi_one[3];
  double *x;

  int dim = domain->dimension;

  int istart,istop,idelta;
  Line *linelist;
  Tri *trilist;

  if (!distributed) {
    istart = me;
    istop = nlocal;
    idelta = nprocs;
    linelist = lines;
    trilist = tris;
  } else {
    istart = 0;
    istop = nown;
    idelta = 1;
    linelist = mylines;
    trilist = mytris;
  }

  for (j = 0; j < 3; j++) {
    bblo_one[j] = BIG;
    bbhi_one[j] = -BIG;
  }

  if (dim == 2) {
    for (i = istart; i < istop; i += idelta) {
      x = linelist[i].p1;
      for (j = 0; j < 2; j++) {
        bblo_one[j] = MIN(bblo_one[j],x[j]);
        bbhi_one[j] = MAX(bbhi_one[j],x[j]);
      }
      x = linelist[i].p2;
      for (j = 0; j < 2; j++) {
        bblo_one[j] = MIN(bblo_one[j],x[j]);
        bbhi_one[j] = MAX(bbhi_one[j],x[j]);
      }
    }
    bblo_one[2] = domain->boxlo[2];
    bbhi_one[2] = domain->boxhi[2];

  } else if (dim == 3) {
    for (i = istart; i < istop; i += idelta) {
      x = trilist[i].p1;
      for (j = 0; j < 3; j++) {
        bblo_one[j] = MIN(bblo_one[j],x[j]);
        bbhi_one[j] = MAX(bbhi_one[j],x[j]);
      }
      x = trilist[i].p2;
      for (j = 0; j < 3; j++) {
        bblo_one[j] = MIN(bblo_one[j],x[j]);
        bbhi_one[j] = MAX(bbhi_one[j],x[j]);
      }
      x = trilist[i].p3;
      for (j = 0; j < 3; j++) {
        bblo_one[j] = MIN(bblo_one[j],x[j]);
        bbhi_one[j] = MAX(bbhi_one[j],x[j]);
      }
    }
  }

  MPI_Allreduce(bblo_one,bblo,3,MPI_DOUBLE,MPI_MIN,world);
  MPI_Allreduce(bbhi_one,bbhi,3,MPI_DOUBLE,MPI_MAX,world);
}

/* ----------------------------------------------------------------------
   set bounding box around one surf based on their pts
   caller passes in the Line or Tri, can be from lines/tris or mylines/mytris
   returns lo,hi which are allocated by caller
   for 2d, set zlo,zhi to box bounds
   only called when surfs = explict (all or distributed)
------------------------------------------------------------------------- */

void Surf::bbox_one(void *ptr, double *lo, double *hi)
{
  double *p1,*p2,*p3;

  if (domain->dimension == 2) {
    Line *line = (Line *) ptr;
    p1 = line->p1; p2 = line->p2;
    lo[0] = MIN(p1[0],p2[0]);
    lo[1] = MIN(p1[1],p2[1]);
    lo[2] = 0.0;
    hi[0] = MAX(p1[0],p2[0]);
    hi[1] = MAX(p1[1],p2[1]);
    hi[2] = 0.0;

  } else {
    Tri *tri = (Tri *) ptr;
    p1 = tri->p1; p2 = tri->p2; p3 = tri->p3;
    lo[0] = MIN(p1[0],p2[0]);
    lo[0] = MIN(lo[0],p3[0]);
    lo[1] = MIN(p1[1],p2[1]);
    lo[1] = MIN(lo[1],p3[1]);
    lo[2] = MIN(p1[2],p2[2]);
    lo[2] = MIN(lo[2],p3[2]);
    hi[0] = MAX(p1[0],p2[0]);
    hi[0] = MAX(hi[0],p3[0]);
    hi[1] = MAX(p1[1],p2[1]);
    hi[1] = MAX(hi[1],p3[1]);
    hi[2] = MAX(p1[2],p2[2]);
    hi[2] = MAX(hi[2],p3[2]);
  }
}

/* ----------------------------------------------------------------------
   compute unit outward normal vectors of all lines starting at Nold
   outward normal = +z axis x (p2-p1)
------------------------------------------------------------------------- */

void Surf::compute_line_normal(int old)
{
  double z[3],delta[3];

  z[0] = 0.0; z[1] = 0.0; z[2] = 1.0;

  int n;
  Line *newlines;

  if (!implicit && distributed) {
    newlines = mylines;
    n = nown;
  } else {
    newlines = lines;
    n = nlocal;
  }

  for (int i = old; i < n; i++) {
    MathExtra::sub3(newlines[i].p2,newlines[i].p1,delta);
    MathExtra::cross3(z,delta,newlines[i].norm);
    MathExtra::norm3(newlines[i].norm);
    newlines[i].norm[2] = 0.0;
  }
}

/* ----------------------------------------------------------------------
   compute unit outward normal vectors of all lines starting at Nold
   outward normal = (p2-p1) x (p3-p1)
------------------------------------------------------------------------- */

void Surf::compute_tri_normal(int old)
{
  int p1,p2,p3;
  double delta12[3],delta13[3];

  int n;
  Tri *newtris;

  if (!implicit && distributed) {
    newtris = mytris;
    n = nown;
  } else {
    newtris = tris;
    n = nlocal;
  }

  for (int i = old; i < n; i++) {
    MathExtra::sub3(newtris[i].p2,newtris[i].p1,delta12);
    MathExtra::sub3(newtris[i].p3,newtris[i].p1,delta13);
    MathExtra::cross3(delta12,delta13,newtris[i].norm);
    MathExtra::norm3(newtris[i].norm);
  }
}

/* ----------------------------------------------------------------------
   return coords of a corner point in a 2d quad
   icorner pts 1 to 4 are ordered by x, then by y
------------------------------------------------------------------------- */

void Surf::quad_corner_point(int icorner, double *lo, double *hi, double *pt)
{
  if (icorner % 2) pt[0] = hi[0];
  else pt[0] = lo[0];
  if (icorner / 2) pt[1] = hi[1];
  else pt[1] = lo[1];
  pt[2] = 0.0;
}

/* ----------------------------------------------------------------------
   return coords of a corner point in a 3d hex
   icorner pts 1 to 8 are ordered by x, then by y, then by z
------------------------------------------------------------------------- */

void Surf::hex_corner_point(int icorner, double *lo, double *hi, double *pt)
{
  if (icorner % 2) pt[0] = hi[0];
  else pt[0] = lo[0];
  if ((icorner/2) % 2) pt[1] = hi[1];
  else pt[1] = lo[1];
  if (icorner / 4) pt[2] = hi[2];
  else pt[2] = lo[2];
}

/* ----------------------------------------------------------------------
   return length of line M from lines list (not myline)
------------------------------------------------------------------------- */

double Surf::line_size(int m)
{
  return line_size(lines[m].p1,lines[m].p2);
}

/* ----------------------------------------------------------------------
   return length of line
------------------------------------------------------------------------- */

double Surf::line_size(Line *line)
{
  return line_size(line->p1,line->p2);
}

/* ----------------------------------------------------------------------
   return length of line bewteen 2 points
------------------------------------------------------------------------- */

double Surf::line_size(double *p1, double *p2)
{
  double delta[3];
  MathExtra::sub3(p2,p1,delta);
  return MathExtra::len3(delta);
}

/* ----------------------------------------------------------------------
   return area associated with rotating axisymmetric line around y=0 axis
------------------------------------------------------------------------- */

double Surf::axi_line_size(int m)
{
  double *x1 = lines[m].p1;
  double *x2 = lines[m].p2;
  double h = x2[0]-x1[0];
  double r = x2[1]-x1[1];
  double area = MY_PI*(x1[1]+x2[1])*sqrt(r*r+h*h);
  return area;
}

/* ----------------------------------------------------------------------
   return area associated with rotating axisymmetric line around y=0 axis
------------------------------------------------------------------------- */

double Surf::axi_line_size(Line *line)
{
  double *x1 = line->p1;
  double *x2 = line->p2;
  double h = x2[0]-x1[0];
  double r = x2[1]-x1[1];
  double area = MY_PI*(x1[1]+x2[1])*sqrt(r*r+h*h);
  return area;
}

/* ----------------------------------------------------------------------
   compute side length and area of triangle M from tri list (not mytri)
   return len = length of shortest edge of triangle M
   return area = area of triangle M
------------------------------------------------------------------------- */

double Surf::tri_size(int m, double &len)
{
  return tri_size(tris[m].p1,tris[m].p2,tris[m].p3,len);
}

/* ----------------------------------------------------------------------
   compute side length and area of triangle tri
   return len = length of shortest edge of triangle M
   return area = area of triangle M
------------------------------------------------------------------------- */

double Surf::tri_size(Tri *tri, double &len)
{
  return tri_size(tri->p1,tri->p2,tri->p3,len);
}

/* ----------------------------------------------------------------------
   compute side length and area of a triangle
   return len = length of shortest edge of triangle M
   return area = area of triangle M
------------------------------------------------------------------------- */

double Surf::tri_size(double *p1, double *p2, double *p3, double &len)
{
  double delta12[3],delta13[3],delta23[3],cross[3];

  MathExtra::sub3(p2,p1,delta12);
  MathExtra::sub3(p3,p1,delta13);
  MathExtra::sub3(p3,p2,delta23);
  len = MIN(MathExtra::len3(delta12),MathExtra::len3(delta13));
  len = MIN(len,MathExtra::len3(delta23));

  MathExtra::cross3(delta12,delta13,cross);
  double area = 0.5 * MathExtra::len3(cross);
  return area;
}

/* ----------------------------------------------------------------------
   check if 2d surf elements are watertight
   each end point should appear exactly once as different ends of 2 lines
   exception: not required of end points on simulation box surface
------------------------------------------------------------------------- */

void Surf::check_watertight_2d()
{
  if (distributed) check_watertight_2d_distributed();
  else check_watertight_2d_all();
}

/* ----------------------------------------------------------------------
   check if 2d surf elements are watertight
   this is for explicit non-distributed surfs where each proc has copy of all
   each proc tests the entire surface, no communication needed
------------------------------------------------------------------------- */

void Surf::check_watertight_2d_all()
{
  // hash end points of all lines
  // key = end point
  // value = 1 if first point, 2 if second point, 3 if both points

  MyHashPoint phash;
  MyPointIt it;

  // insert each end point into hash
  // should appear once at each end
  // error if any duplicate points

  double *p1,*p2;
  OnePoint2d key;
  int value;

  int ndup = 0;
  for (int i = 0; i < nsurf; i++) {
    if (lines[i].transparent) continue;
    p1 = lines[i].p1;
    key.pt[0] = p1[0]; key.pt[1] = p1[1];
    if (phash.find(key) == phash.end()) phash[key] = 1;
    else {
      value = phash[key];
      if (value == 2) phash[key] = 3;
      else ndup++;
    }

    p2 = lines[i].p2;
    key.pt[0] = p2[0]; key.pt[1] = p2[1];
    if (phash.find(key) == phash.end()) phash[key] = 2;
    else {
      value = phash[key];
      if (value == 1) phash[key] = 3;
      else ndup++;
    }
  }

  if (ndup) {
    char str[128];
    sprintf(str,"Watertight check failed with %d duplicate points",ndup);
    error->all(FLERR,str);
  }

  // check that each end point has a match (value = 3)
  // allow for exception if end point on box surface

  double *boxlo = domain->boxlo;
  double *boxhi = domain->boxhi;
  double *kpt;
  double pt[3];

  int nbad = 0;
  for (it = phash.begin(); it != phash.end(); ++it) {
    if (it->second != 3) {
      kpt = (double *) it->first.pt;
      pt[0] = kpt[0]; pt[1] = kpt[1]; pt[2] = 0.0;
      if (!Geometry::point_on_hex(pt,boxlo,boxhi)) nbad++;
    }
  }

  if (nbad) {
    char str[128];
    sprintf(str,"Watertight check failed with %d unmatched points",nbad);
    error->all(FLERR,str);
  }
}

/* ----------------------------------------------------------------------
   check if 2d surf elements are watertight
   this is for explicit distributed surfs
   rendezvous communication used to check that each point appears twice
------------------------------------------------------------------------- */

void Surf::check_watertight_2d_distributed()
{
  int n;
  Line *lines_rvous;

  if (implicit) {
    n = nlocal;
    lines_rvous = lines;
  } else {
    n = nown;
    lines_rvous = mylines;
  }

  // allocate memory for rvous input

  int *proclist;
  memory->create(proclist,n*2,"surf:proclist");
  InRvousPoint *inpoint =
    (InRvousPoint *) memory->smalloc((bigint) n*2*sizeof(InRvousPoint),
                                     "surf:inpoint");

  // create rvous inputs
  // proclist = owner of each point
  // each line end point is sent with flag indicating first/second
  // hash of point coord (xy) determines which proc to send to

  int nrvous = 0;
  for (int i = 0; i < n; i++) {
    proclist[nrvous] = hashlittle(lines_rvous[i].p1,2*sizeof(double),0) % nprocs;
    inpoint[nrvous].x[0] = lines_rvous[i].p1[0];
    inpoint[nrvous].x[1] = lines_rvous[i].p1[1];
    inpoint[nrvous].which = 1;
    nrvous++;
    proclist[nrvous] = hashlittle(lines_rvous[i].p2,2*sizeof(double),0) % nprocs;
    inpoint[nrvous].x[0] = lines_rvous[i].p2[0];
    inpoint[nrvous].x[1] = lines_rvous[i].p2[1];
    inpoint[nrvous].which = 2;
    nrvous++;
  }

  // perform rendezvous operation
  // each proc assigned subset of points
  // receives all copies of points, checks if count of each point is valid

  char *buf;
  int nout = comm->rendezvous(1,nrvous,(char *) inpoint,sizeof(InRvousPoint),
                              0,proclist,rendezvous_watertight_2d,
                              0,buf,0,(void *) this);

  memory->destroy(proclist);
  memory->destroy(inpoint);
}

/* ----------------------------------------------------------------------
   callback from rendezvous operation
   process points assigned to me
   inbuf = list of N Inbuf datums
   no outbuf
------------------------------------------------------------------------- */

int Surf::rendezvous_watertight_2d(int n, char *inbuf, int &flag, int *&proclist,
                                   char *&outbuf, void *ptr)
{
  Surf *sptr = (Surf *) ptr;
  Domain *domain = sptr->domain;
  Error *error = sptr->error;
  MPI_Comm world = sptr->world;

  Surf::InRvousPoint *inpoint = (Surf::InRvousPoint *) inbuf;

  // hash all received end points
  // key = end point
  // value = 1 if first point, 2 if second point, 3 if both points

  Surf::MyHashPoint phash;
  Surf::MyPointIt it;

  // insert each point into hash
  // should appear once at each end of a line
  // error if any duplicate points

  Surf::OnePoint2d key;
  int which,value;

  int ndup = 0;
  for (int i = 0; i < n; i++) {
    key.pt[0] = inpoint[i].x[0]; key.pt[1] = inpoint[i].x[1];
    which = inpoint[i].which;
    if (phash.find(key) == phash.end()) phash[key] = which;
    else {
      value = phash[key];
      if (value == 3) ndup++;    // point already seen twice
      else if (value != which) phash[key] = 3;   // this is other point
      else ndup++;               // value = which, this is duplicate point
    }
  }

  int alldup;
  MPI_Allreduce(&ndup,&alldup,1,MPI_INT,MPI_SUM,world);
  if (alldup) {
    char str[128];
    sprintf(str,"Watertight check failed with %d duplicate points",alldup);
    error->all(FLERR,str);
  }

  // check that each end point has a match (value = 3)
  // allow for exception if end point on box surface

  double *boxlo = domain->boxlo;
  double *boxhi = domain->boxhi;
  double *kpt;
  double pt[3];

  int nbad = 0;
  for (it = phash.begin(); it != phash.end(); ++it) {
    if (it->second != 3) {
      kpt = (double *) it->first.pt;
      pt[0] = kpt[0]; pt[1] = kpt[1]; pt[2] = 0.0;
      if (!Geometry::point_on_hex(pt,boxlo,boxhi)) nbad++;
    }
  }

  int allbad;
  MPI_Allreduce(&nbad,&allbad,1,MPI_INT,MPI_SUM,world);
  if (nbad) {
    char str[128];
    sprintf(str,"Watertight check failed with %d unmatched points",allbad);
    error->all(FLERR,str);
  }

  // flag = 0: no second comm needed in rendezvous

  flag = 0;
  return 0;
}

/* ----------------------------------------------------------------------
   check if 3d surf elements are watertight
   each edge should appear exactly once in each direction
   exception: not required of triangle edge on simulation box surface
------------------------------------------------------------------------- */

void Surf::check_watertight_3d()
{
  if (distributed) check_watertight_3d_distributed();
  else check_watertight_3d_all();
}

/* ----------------------------------------------------------------------
   check if 3d surf elements are watertight
   this is for explicit non-distributed surfs where each proc has copy of all
   each proc tests the entire surface, no communication needed
------------------------------------------------------------------------- */

void Surf::check_watertight_3d_all()
{
  // hash directed edges of all triangles
  // key = directed edge
  // value = 1 if appears once, 2 if reverse also appears once

  MyHash2Point phash;
  My2PointIt it;

  // insert each edge into hash
  // should appear once in each direction
  // error if any duplicate edges

  double *p1,*p2,*p3;
  TwoPoint3d key,keyinv;
  int value;

  int ndup = 0;
  for (int i = 0; i < nsurf; i++) {
    if (tris[i].transparent) continue;
    p1 = tris[i].p1;
    p2 = tris[i].p2;
    p3 = tris[i].p3;

    key.pts[0] = p1[0]; key.pts[1] = p1[1]; key.pts[2] = p1[2];
    key.pts[3] = p2[0]; key.pts[4] = p2[1]; key.pts[5] = p2[2];
    if (phash.find(key) == phash.end()) {
      keyinv.pts[0] = p2[0]; keyinv.pts[1] = p2[1]; keyinv.pts[2] = p2[2];
      keyinv.pts[3] = p1[0]; keyinv.pts[4] = p1[1]; keyinv.pts[5] = p1[2];
      if (phash.find(keyinv) == phash.end()) phash[key] = 1;
      else {
        value = phash[keyinv];
        if (value == 1) phash[keyinv] = 2;
        else ndup++;
      }
    } else ndup++;

    key.pts[0] = p2[0]; key.pts[1] = p2[1]; key.pts[2] = p2[2];
    key.pts[3] = p3[0]; key.pts[4] = p3[1]; key.pts[5] = p3[2];
    if (phash.find(key) == phash.end()) {
      keyinv.pts[0] = p3[0]; keyinv.pts[1] = p3[1]; keyinv.pts[2] = p3[2];
      keyinv.pts[3] = p2[0]; keyinv.pts[4] = p2[1]; keyinv.pts[5] = p2[2];
      if (phash.find(keyinv) == phash.end()) phash[key] = 1;
      else {
        value = phash[keyinv];
        if (value == 1) phash[keyinv] = 2;
        else ndup++;
      }
    } else ndup++;

    key.pts[0] = p3[0]; key.pts[1] = p3[1]; key.pts[2] = p3[2];
    key.pts[3] = p1[0]; key.pts[4] = p1[1]; key.pts[5] = p1[2];
    if (phash.find(key) == phash.end()) {
      keyinv.pts[0] = p1[0]; keyinv.pts[1] = p1[1]; keyinv.pts[2] = p1[2];
      keyinv.pts[3] = p3[0]; keyinv.pts[4] = p3[1]; keyinv.pts[5] = p3[2];
      if (phash.find(keyinv) == phash.end()) phash[key] = 1;
      else {
        value = phash[keyinv];
        if (value == 1) phash[keyinv] = 2;
        else ndup++;
      }
    } else ndup++;
  }

  if (ndup) {
    char str[128];
    sprintf(str,"Watertight check failed with %d duplicate edges",ndup);
    error->all(FLERR,str);
  }

  // check that each edge has an inverted match
  // allow for exception if edge is on box face

  double *boxlo = domain->boxlo;
  double *boxhi = domain->boxhi;
  double *pts;

  int nbad = 0;
  for (it = phash.begin(); it != phash.end(); ++it) {
    if (it->second != 2) {
      pts = (double *) it->first.pts;
      if (Geometry::edge_on_hex_face(&pts[0],&pts[3],boxlo,boxhi) < 0) nbad++;
    }
  }

  if (nbad) {
    char str[128];
    sprintf(str,"Watertight check failed with %d unmatched edges",nbad);
    error->all(FLERR,str);
  }
}

/* ----------------------------------------------------------------------
   check if 3d surf elements are watertight
   this is for explicit distributed surfs
   rendezvous communication used to check that each edge appears twice
------------------------------------------------------------------------- */

void Surf::check_watertight_3d_distributed()
{
  int n;
  Tri *tris_rvous;

  if (implicit) {
    n = nlocal;
    tris_rvous = tris;
  } else {
    n = nown;
    tris_rvous = mytris;
  }

  // allocate memory for rvous input

  int *proclist;
  memory->create(proclist,n*6,"surf:proclist");
  InRvousEdge *inedge =
    (InRvousEdge *) memory->smalloc((bigint) n*6*sizeof(InRvousEdge),
                                     "surf:inedge");

  // create rvous inputs
  // proclist = owner of each point
  // each triangle edge is sent twice with flag indicating
  //   forward or reverse order
  // hash of edge coords (xyz for 2 pts) determines which proc to send to

  double edge[6];
  double *p1,*p2,*p3;

  int nbytes = 3*sizeof(double);

  int nrvous = 0;
  for (int i = 0; i < n; i++) {
    p1 = tris_rvous[i].p1;
    p2 = tris_rvous[i].p2;
    p3 = tris_rvous[i].p3;

    memcpy(&edge[0],p1,nbytes);
    memcpy(&edge[3],p2,nbytes);
    proclist[nrvous] = hashlittle(edge,2*nbytes,0) % nprocs;
    memcpy(inedge[nrvous].x1,p1,nbytes);
    memcpy(inedge[nrvous].x2,p2,nbytes);
    inedge[nrvous].which = 1;
    nrvous++;

    memcpy(&edge[0],p2,nbytes);
    memcpy(&edge[3],p1,nbytes);
    proclist[nrvous] = hashlittle(edge,2*nbytes,0) % nprocs;
    memcpy(inedge[nrvous].x1,p2,nbytes);
    memcpy(inedge[nrvous].x2,p1,nbytes);
    inedge[nrvous].which = 2;
    nrvous++;

    memcpy(&edge[0],p2,nbytes);
    memcpy(&edge[3],p3,nbytes);
    proclist[nrvous] = hashlittle(edge,2*nbytes,0) % nprocs;
    memcpy(inedge[nrvous].x1,p2,nbytes);
    memcpy(inedge[nrvous].x2,p3,nbytes);
    inedge[nrvous].which = 1;
    nrvous++;

    memcpy(&edge[0],p3,nbytes);
    memcpy(&edge[3],p2,nbytes);
    proclist[nrvous] = hashlittle(edge,2*nbytes,0) % nprocs;
    memcpy(inedge[nrvous].x1,p3,nbytes);
    memcpy(inedge[nrvous].x2,p2,nbytes);
    inedge[nrvous].which = 2;
    nrvous++;

    memcpy(&edge[0],p3,nbytes);
    memcpy(&edge[3],p1,nbytes);
    proclist[nrvous] = hashlittle(edge,2*nbytes,0) % nprocs;
    memcpy(inedge[nrvous].x1,p3,nbytes);
    memcpy(inedge[nrvous].x2,p1,nbytes);
    inedge[nrvous].which = 1;
    nrvous++;

    memcpy(&edge[0],p1,nbytes);
    memcpy(&edge[3],p3,nbytes);
    proclist[nrvous] = hashlittle(edge,2*nbytes,0) % nprocs;
    memcpy(inedge[nrvous].x1,p1,nbytes);
    memcpy(inedge[nrvous].x2,p3,nbytes);
    inedge[nrvous].which = 2;
    nrvous++;
  }

  // perform rendezvous operation
  // each proc assigned subset of edges
  // receives all copies of edges, checks if count of each edge is valid

  char *buf;
  int nout = comm->rendezvous(1,nrvous,(char *) inedge,sizeof(InRvousEdge),
                              0,proclist,rendezvous_watertight_3d,
                              0,buf,0,(void *) this);

  memory->destroy(proclist);
  memory->destroy(inedge);
}

/* ----------------------------------------------------------------------
   callback from rendezvous operation
   process points assigned to me
   inbuf = list of N Inbuf datums
   no outbuf
------------------------------------------------------------------------- */

int Surf::rendezvous_watertight_3d(int n, char *inbuf, int &flag, int *&proclist,
                                   char *&outbuf, void *ptr)
{
  Surf *sptr = (Surf *) ptr;
  Domain *domain = sptr->domain;
  Error *error = sptr->error;
  MPI_Comm world = sptr->world;

  Surf::InRvousEdge *inedge = (Surf::InRvousEdge *) inbuf;

  // hash all received end points
  // key = end point
  // value = 1 if first point, 2 if second point, 3 if both points

  Surf::MyHash2Point phash;
  Surf::My2PointIt it;

  // insert each edge into hash
  // should appear once in each direction
  // error if any duplicate edges

  Surf::TwoPoint3d key;
  double *x1,*x2;
  int which,value;

  int ndup = 0;
  for (int i = 0; i < n; i++) {
    x1 = inedge[i].x1; x2 = inedge[i].x2;
    key.pts[0] = x1[0]; key.pts[1] = x1[1]; key.pts[2] = x1[2];
    key.pts[3] = x2[0]; key.pts[4] = x2[1]; key.pts[5] = x2[2];
    which = inedge[i].which;
    if (phash.find(key) == phash.end()) phash[key] = which;
    else {
      value = phash[key];
      if (value == 3) ndup++;    // edge already seen twice
      else if (value != which) phash[key] = 3;   // this is flipped edge
      else ndup++;               // value = which, this is duplicate edge
    }
  }

  int alldup;
  MPI_Allreduce(&ndup,&alldup,1,MPI_INT,MPI_SUM,world);
  alldup /= 2;              // avoid double counting
  if (alldup) {
    char str[128];
    sprintf(str,"Watertight check failed with %d duplicate edges",alldup);
    error->all(FLERR,str);
  }

  // check that each edge has an inverted match(value = 3)
  // allow for exception if edge is on box face

  double *boxlo = domain->boxlo;
  double *boxhi = domain->boxhi;
  double *pts;

  int nbad = 0;
  for (it = phash.begin(); it != phash.end(); ++it) {
    if (it->second != 3) {
      pts = (double *) it->first.pts;
      if (Geometry::edge_on_hex_face(&pts[0],&pts[3],boxlo,boxhi) < 0) nbad++;
    }
  }

  int allbad;
  MPI_Allreduce(&nbad,&allbad,1,MPI_INT,MPI_SUM,world);
  allbad /= 2;              // avoid double counting
  if (nbad) {
    char str[128];
    sprintf(str,"Watertight check failed with %d unmatched edges",allbad);
    error->all(FLERR,str);
  }

  // flag = 0: no second comm needed in rendezvous

  flag = 0;
  return 0;
}

/* ----------------------------------------------------------------------
   check if all points are inside or on surface of global simulation box
   called by ReadSurf for lines or triangles
   old = previous # of elements
------------------------------------------------------------------------- */

void Surf::check_point_inside(int old)
{
  int nbad;
  double *x;

  int dim = domain->dimension;
  double *boxlo = domain->boxlo;
  double *boxhi = domain->boxhi;

  if (dim == 2) {
    Line *newlines;
    int n;
    if (distributed) {
      newlines = mylines;
      n = nown;
    } else {
      newlines = lines;
      n = nlocal;
    }

    nbad = 0;
    for (int i = old; i < n; i++) {
      x = newlines[i].p1;
      if (x[0] < boxlo[0] || x[0] > boxhi[0] ||
          x[1] < boxlo[1] || x[1] > boxhi[1] ||
          x[2] < boxlo[2] || x[2] > boxhi[2]) nbad++;
      x = newlines[i].p2;
      if (x[0] < boxlo[0] || x[0] > boxhi[0] ||
          x[1] < boxlo[1] || x[1] > boxhi[1] ||
          x[2] < boxlo[2] || x[2] > boxhi[2]) nbad++;
    }

  } else if (dim == 3) {
    Tri *newtris;
    int n;
    if (distributed) {
      newtris = mytris;
      n = nown;
    } else {
      newtris = tris;
      n = nlocal;
    }

    nbad = 0;
    for (int i = old; i < n; i++) {
      x = newtris[i].p1;
      if (x[0] < boxlo[0] || x[0] > boxhi[0] ||
          x[1] < boxlo[1] || x[1] > boxhi[1] ||
          x[2] < boxlo[2] || x[2] > boxhi[2]) nbad++;
      x = newtris[i].p2;
      if (x[0] < boxlo[0] || x[0] > boxhi[0] ||
          x[1] < boxlo[1] || x[1] > boxhi[1] ||
          x[2] < boxlo[2] || x[2] > boxhi[2]) nbad++;
      x = newtris[i].p3;
      if (x[0] < boxlo[0] || x[0] > boxhi[0] ||
          x[1] < boxlo[1] || x[1] > boxhi[1] ||
          x[2] < boxlo[2] || x[2] > boxhi[2]) nbad++;
    }
  }

  int nbadall;
  if (distributed) MPI_Allreduce(&nbad,&nbadall,1,MPI_INT,MPI_SUM,world);
  else nbadall = nbad;

  if (nbadall) {
    char str[128];
    sprintf(str,"%d surface points are not inside simulation box",
            nbadall);
    error->all(FLERR,str);
  }
}

/* ----------------------------------------------------------------------
   check nearness of all points to other lines in same cell
   error if point is on line, including duplicate point
   warn if closer than EPSILON_GRID = fraction of grid cell size
   NOTE: this can miss a close point/line pair in 2 different grid cells
------------------------------------------------------------------------- */

void Surf::check_point_near_surf_2d()
{
  int i,j,n;
  surfint *csurfs;
  double side,epssq;
  double *p1,*p2,*lo,*hi;
  Surf::Line *line;

  Surf::Line *lines = surf->lines;
  Grid::ChildCell *cells = grid->cells;
  int nglocal = grid->nlocal;

  int nerror = 0;
  int nwarn = 0;

  for (int icell = 0; icell < nglocal; icell++) {
    if (cells[icell].nsplit <= 0) continue;
    n = cells[icell].nsurf;
    if (n == 0) continue;

    lo = cells[icell].lo;
    hi = cells[icell].hi;
    side = MIN(hi[0]-lo[0],hi[1]-lo[1]);
    epssq = (EPSILON_GRID*side) * (EPSILON_GRID*side);

    csurfs = cells[icell].csurfs;
    for (i = 0; i < n; i++) {
      line = &lines[csurfs[i]];
      // skip transparent surf elements
      if (line->transparent) continue;
      for (j = 0; j < n; j++) {
        if (i == j) continue;
        p1 = lines[csurfs[j]].p1;
        p2 = lines[csurfs[j]].p2;
        point_line_compare(p1,line->p1,line->p2,epssq,nerror,nwarn);
        point_line_compare(p2,line->p1,line->p2,epssq,nerror,nwarn);
      }
    }
  }

  int all;
  MPI_Allreduce(&nerror,&all,1,MPI_INT,MPI_SUM,world);
  if (all) {
    char str[128];
    sprintf(str,"Surface check failed with %d points on lines",all);
    error->all(FLERR,str);
  }

  MPI_Allreduce(&nwarn,&all,1,MPI_INT,MPI_SUM,world);
  if (all) {
    char str[128];
    sprintf(str,"Surface check found %d points nearly on lines",all);
    if (comm->me == 0) error->warning(FLERR,str);
  }
}

/* ----------------------------------------------------------------------
   check nearness of all points to other triangles in same cell
   error if point is on triangle, including duplicate point
   warn if closer than EPSILON_GRID = fraction of grid cell size
   NOTE: this can miss a close point/triangle pair in 2 different grid cells
------------------------------------------------------------------------- */

void Surf::check_point_near_surf_3d()
{
  int i,j,n;
  surfint *csurfs;
  double side,epssq;
  double *p1,*p2,*p3,*lo,*hi;
  Surf::Tri *tri;

  Surf::Tri *tris = surf->tris;
  Grid::ChildCell *cells = grid->cells;
  int nglocal = grid->nlocal;

  int nerror = 0;
  int nwarn = 0;

  for (int icell = 0; icell < nglocal; icell++) {
    if (cells[icell].nsplit <= 0) continue;
    n = cells[icell].nsurf;
    if (n == 0) continue;

    lo = cells[icell].lo;
    hi = cells[icell].hi;
    side = MIN(hi[0]-lo[0],hi[1]-lo[1]);
    side = MIN(side,hi[2]-lo[2]);
    epssq = (EPSILON_GRID*side) * (EPSILON_GRID*side);

    csurfs = cells[icell].csurfs;
    for (i = 0; i < n; i++) {
      tri = &tris[csurfs[i]];
      // skip transparent surf elements
      if (tri->transparent) continue;
      for (j = 0; j < n; j++) {
        if (i == j) continue;
        p1 = tris[csurfs[j]].p1;
        p2 = tris[csurfs[j]].p2;
        p3 = tris[csurfs[j]].p3;
        point_tri_compare(p1,tri->p1,tri->p2,tri->p3,tri->norm,
                          epssq,nerror,nwarn,icell,csurfs[i],csurfs[j]);
        point_tri_compare(p2,tri->p1,tri->p2,tri->p3,tri->norm,
                          epssq,nerror,nwarn,icell,csurfs[i],csurfs[j]);
        point_tri_compare(p3,tri->p1,tri->p2,tri->p3,tri->norm,
                          epssq,nerror,nwarn,icell,csurfs[i],csurfs[j]);
      }
    }
  }

  int all;
  MPI_Allreduce(&nerror,&all,1,MPI_INT,MPI_SUM,world);
  if (all) {
    char str[128];
    sprintf(str,"Surface check failed with %d points on triangles",all);
    error->all(FLERR,str);
  }

  MPI_Allreduce(&nwarn,&all,1,MPI_INT,MPI_SUM,world);
  if (all) {
    char str[128];
    sprintf(str,"Surface check found %d points nearly on triangles",all);
    if (comm->me == 0) error->warning(FLERR,str);
  }
}

/* ----------------------------------------------------------------------
   compute extent of read-in surfs, including geometric transformations
------------------------------------------------------------------------- */

void Surf::output_extent(int old)
{
  // extent of surfs after geometric transformations
  // compute sizes of smallest surface elements

  double extent[3][2],extentall[3][2];
  extent[0][0] = extent[1][0] = extent[2][0] = BIG;
  extent[0][1] = extent[1][1] = extent[2][1] = -BIG;

  int dim = domain->dimension;

  if (dim == 2) {
    Line *newlines;
    int n;
    if (!implicit && distributed) {
      newlines = mylines;
      n = nown;
    } else {
      newlines = lines;
      n = nlocal;
    }

    for (int i = old; i < n; i++) {
      for (int j = 0; j < 3; j++) {
        extent[j][0] = MIN(extent[j][0],newlines[i].p1[j]);
        extent[j][0] = MIN(extent[j][0],newlines[i].p2[j]);
        extent[j][1] = MAX(extent[j][1],newlines[i].p1[j]);
        extent[j][1] = MAX(extent[j][1],newlines[i].p2[j]);
      }
    }

  } else {
    Tri *newtris;
    int n;
    if (!implicit && distributed) {
      newtris = mytris;
      n = nown;
    } else {
      newtris = tris;
      n = nlocal;
    }

    for (int i = old; i < n; i++) {
      for (int j = 0; j < 3; j++) {
        extent[j][0] = MIN(extent[j][0],newtris[i].p1[j]);
        extent[j][0] = MIN(extent[j][0],newtris[i].p2[j]);
        extent[j][0] = MIN(extent[j][0],newtris[i].p3[j]);
        extent[j][1] = MAX(extent[j][1],newtris[i].p1[j]);
        extent[j][1] = MAX(extent[j][1],newtris[i].p2[j]);
        extent[j][1] = MAX(extent[j][1],newtris[i].p3[j]);
      }
    }
  }

  extent[0][0] = -extent[0][0];
  extent[1][0] = -extent[1][0];
  extent[2][0] = -extent[2][0];
  MPI_Allreduce(extent,extentall,6,MPI_DOUBLE,MPI_MAX,world);
  extentall[0][0] = -extentall[0][0];
  extentall[1][0] = -extentall[1][0];
  extentall[2][0] = -extentall[2][0];

  double minlen,minarea;
  if (dim == 2) minlen = shortest_line(old);
  if (dim == 3) smallest_tri(old,minlen,minarea);

  if (comm->me == 0) {
    if (screen) {
      fprintf(screen,"  %g %g xlo xhi\n",extentall[0][0],extentall[0][1]);
      fprintf(screen,"  %g %g ylo yhi\n",extentall[1][0],extentall[1][1]);
      fprintf(screen,"  %g %g zlo zhi\n",extentall[2][0],extentall[2][1]);
      if (dim == 2)
        fprintf(screen,"  %g min line length\n",minlen);
      if (dim == 3) {
        fprintf(screen,"  %g min triangle edge length\n",minlen);
        fprintf(screen,"  %g min triangle area\n",minarea);
      }
    }
    if (logfile) {
      fprintf(logfile,"  %g %g xlo xhi\n",extentall[0][0],extentall[0][1]);
      fprintf(logfile,"  %g %g ylo yhi\n",extentall[1][0],extentall[1][1]);
      fprintf(logfile,"  %g %g zlo zhi\n",extentall[2][0],extentall[2][1]);
      if (dim == 2)
        fprintf(logfile,"  %g min line length\n",minlen);
      if (dim == 3) {
        fprintf(logfile,"  %g min triangle edge length\n",minlen);
        fprintf(logfile,"  %g min triangle area\n",minarea);
      }
    }
  }
}

/* ----------------------------------------------------------------------
   return shortest line length
------------------------------------------------------------------------- */

double Surf::shortest_line(int old)
{
  double len = BIG;

  if (!implicit && distributed) {
    for (int i = old; i < nown; i++)
      len = MIN(len,line_size(&mylines[i]));
  } else {
    for (int i = old; i < nlocal; i++)
      len = MIN(len,line_size(&lines[i]));
  }

  double lenall;
  MPI_Allreduce(&len,&lenall,1,MPI_DOUBLE,MPI_MIN,world);

  return lenall;
}

/* ----------------------------------------------------------------------
   return shortest tri edge and smallest tri area
------------------------------------------------------------------------- */

void Surf::smallest_tri(int old, double &lenall, double &areaall)
{
  double lenone,areaone;
  double len = BIG;
  double area = BIG;

  if (!implicit && distributed) {
    for (int i = old; i < nown; i++) {
      areaone = tri_size(&mytris[i],lenone);
      len = MIN(len,lenone);
      area = MIN(area,areaone);
    }
  } else {
    for (int i = old; i < nlocal; i++) {
      areaone = tri_size(&tris[i],lenone);
      len = MIN(len,lenone);
      area = MIN(area,areaone);
    }
  }

  MPI_Allreduce(&len,&lenall,1,MPI_DOUBLE,MPI_MIN,world);
  MPI_Allreduce(&area,&areaall,1,MPI_DOUBLE,MPI_MIN,world);
}

/* ----------------------------------------------------------------------
   compute distance bewteen a point and line
   just return if point is an endpoint of line
   increment nerror if point on line
   increment nwarn if point is within epssq distance of line
------------------------------------------------------------------------- */

void Surf::point_line_compare(double *pt, double *p1, double *p2,
                              double epssq, int &nerror, int &nwarn)
{
  if (pt[0] == p1[0] && pt[1] == p1[1]) return;
  if (pt[0] == p2[0] && pt[1] == p2[1]) return;
  double rsq = Geometry::distsq_point_line(pt,p1,p2);
  if (rsq == 0.0) nerror++;
  else if (rsq < epssq) nwarn++;
}

/* ----------------------------------------------------------------------
   compute distance bewteen a point and triangle
   just return if point is an endpoint of triangle
   increment nerror if point on triangle
   increment nwarn if point is within epssq distance of triangle
------------------------------------------------------------------------- */

void Surf::point_tri_compare(double *pt, double *p1, double *p2, double *p3,
                             double *norm, double epssq, int &nerror, int &nwarn,
                             int, int, int)
{
  if (pt[0] == p1[0] && pt[1] == p1[1] && pt[2] == p1[2]) return;
  if (pt[0] == p2[0] && pt[1] == p2[1] && pt[2] == p2[2]) return;
  if (pt[0] == p3[0] && pt[1] == p3[1] && pt[2] == p3[2]) return;
  double rsq = Geometry::distsq_point_tri(pt,p1,p2,p3,norm);
  if (rsq == 0.0) nerror++;
  else if (rsq < epssq) nwarn++;
}


/* ----------------------------------------------------------------------
   add a surface collision model
------------------------------------------------------------------------- */

void Surf::add_collide(int narg, char **arg)
{
  if (narg < 2) error->all(FLERR,"Illegal surf_collide command");

  // error check

  for (int i = 0; i < nsc; i++)
    if (strcmp(arg[0],sc[i]->id) == 0)
      error->all(FLERR,"Reuse of surf_collide ID");

  // extend SurfCollide list if necessary

  if (nsc == maxsc) {
    maxsc += DELTAMODEL;
    sc = (SurfCollide **)
      memory->srealloc(sc,maxsc*sizeof(SurfCollide *),"surf:sc");
  }

  // create new SurfCollide class

  if (sparta->suffix_enable) {
    if (sparta->suffix) {
      char estyle[256];
      sprintf(estyle,"%s/%s",arg[1],sparta->suffix);

      if (0) return;

#define SURF_COLLIDE_CLASS
#define SurfCollideStyle(key,Class) \
      else if (strcmp(estyle,#key) == 0) { \
        sc[nsc] = new Class(sparta,narg,arg); \
        nsc++; \
        return; \
      }
#include "style_surf_collide.h"
#undef SurfCollideStyle
#undef SURF_COLLIDE_CLASS
    }
  }

  if (0) return;

#define SURF_COLLIDE_CLASS
#define SurfCollideStyle(key,Class) \
  else if (strcmp(arg[1],#key) == 0) \
    sc[nsc] = new Class(sparta,narg,arg);
#include "style_surf_collide.h"
#undef SurfCollideStyle
#undef SURF_COLLIDE_CLASS

  else error->all(FLERR,"Unrecognized surf_collide style");

  nsc++;
}

/* ----------------------------------------------------------------------
   find a surface collide model by ID
   return index of surf collide model or -1 if not found
------------------------------------------------------------------------- */

int Surf::find_collide(const char *id)
{
  int isc;
  for (isc = 0; isc < nsc; isc++)
    if (strcmp(id,sc[isc]->id) == 0) break;
  if (isc == nsc) return -1;
  return isc;
}

/* ----------------------------------------------------------------------
   add a surface reaction model
------------------------------------------------------------------------- */

void Surf::add_react(int narg, char **arg)
{
  if (narg < 2) error->all(FLERR,"Illegal surf_react command");

  // error check

  for (int i = 0; i < nsr; i++)
    if (strcmp(arg[0],sr[i]->id) == 0)
      error->all(FLERR,"Reuse of surf_react ID");

  // extend SurfReact list if necessary

  if (nsr == maxsr) {
    maxsr += DELTAMODEL;
    sr = (SurfReact **)
      memory->srealloc(sr,maxsr*sizeof(SurfReact *),"surf:sr");
  }

  // create new SurfReact class

  if (sparta->suffix_enable) {
    if (sparta->suffix) {
      char estyle[256];
      sprintf(estyle,"%s/%s",arg[1],sparta->suffix);

      if (0) return;

#define SURF_REACT_CLASS
#define SurfReactStyle(key,Class) \
      else if (strcmp(estyle,#key) == 0) { \
        sr[nsr] = new Class(sparta,narg,arg); \
        nsr++; \
        return; \
      }
#include "style_surf_react.h"
#undef SurfReactStyle
#undef SURF_REACT_CLASS
    }
  }

  if (0) return;

#define SURF_REACT_CLASS
#define SurfReactStyle(key,Class) \
  else if (strcmp(arg[1],#key) == 0) \
    sr[nsr] = new Class(sparta,narg,arg);
#include "style_surf_react.h"
#undef SurfReactStyle
#undef SURF_REACT_CLASS

  else error->all(FLERR,"Unrecognized surf_react style");

  nsr++;
}

/* ----------------------------------------------------------------------
   find a surface reaction model by ID
   return index of surf reaction model or -1 if not found
------------------------------------------------------------------------- */

int Surf::find_react(const char *id)
{
  int isr;
  for (isr = 0; isr < nsr; isr++)
    if (strcmp(id,sr[isr]->id) == 0) break;
  if (isr == nsr) return -1;
  return isr;
}

/* ----------------------------------------------------------------------
   group surf command called via input script
   NOTE: need to apply this also to mylines and mytris ??
------------------------------------------------------------------------- */

void Surf::group(int narg, char **arg)
{
  int i,flag;
  double x[3];

  if (narg < 3) error->all(FLERR,"Illegal group command");

  int dim = domain->dimension;

  int igroup = find_group(arg[0]);
  if (igroup < 0) igroup = add_group(arg[0]);
  int bit = bitmask[igroup];

  // style = type or id
  // add surf to group if matches types/ids or condition

  if (strcmp(arg[2],"type") == 0 || strcmp(arg[2],"id") == 0) {
    if (narg < 4) error->all(FLERR,"Illegal group command");

    int category;
    if (strcmp(arg[2],"type") == 0) category = TYPE;
    else if (strcmp(arg[2],"id") == 0) category = ID;

    // args = logical condition

    if (narg > 4 &&
        (strcmp(arg[3],"<") == 0 || strcmp(arg[3],">") == 0 ||
         strcmp(arg[3],"<=") == 0 || strcmp(arg[3],">=") == 0 ||
         strcmp(arg[3],"==") == 0 || strcmp(arg[3],"!=") == 0 ||
         strcmp(arg[3],"<>") == 0)) {

      int condition = -1;
      if (strcmp(arg[3],"<") == 0) condition = LT;
      else if (strcmp(arg[3],"<=") == 0) condition = LE;
      else if (strcmp(arg[3],">") == 0) condition = GT;
      else if (strcmp(arg[3],">=") == 0) condition = GE;
      else if (strcmp(arg[3],"==") == 0) condition = EQ;
      else if (strcmp(arg[3],"!=") == 0) condition = NEQ;
      else if (strcmp(arg[3],"<>") == 0) condition = BETWEEN;
      else error->all(FLERR,"Illegal group command");

      int bound1,bound2;
      bound1 = input->inumeric(FLERR,arg[4]);
      bound2 = -1;

      if (condition == BETWEEN) {
        if (narg != 6) error->all(FLERR,"Illegal group command");
        bound2 = input->inumeric(FLERR,arg[5]);
      } else if (narg != 5) error->all(FLERR,"Illegal group command");

      // add surf to group if meets condition

      if (category == ID) {
        if (condition == LT) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].id < bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].id < bound1) tris[i].mask |= bit;
          }
        } else if (condition == LE) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].id <= bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].id <= bound1) tris[i].mask |= bit;
          }
        } else if (condition == GT) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].id > bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].id > bound1) tris[i].mask |= bit;
          }
        } else if (condition == GE) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].id >= bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].id >= bound1) tris[i].mask |= bit;
          }
        } else if (condition == EQ) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].id == bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].id == bound1) tris[i].mask |= bit;
          }
        } else if (condition == NEQ) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].id != bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].id != bound1) tris[i].mask |= bit;
          }
        } else if (condition == BETWEEN) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].id >= bound1 && lines[i].id <= bound2)
                lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].id >= bound1 && tris[i].id <= bound2)
                tris[i].mask |= bit;
          }
        }
      } else if (category == TYPE) {
        if (condition == LT) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].type < bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].type < bound1) lines[i].mask |= bit;
          }
        } else if (condition == LE) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].type <= bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].type <= bound1) lines[i].mask |= bit;
          }
        } else if (condition == GT) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].type > bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].type > bound1) lines[i].mask |= bit;
          }
        } else if (condition == GE) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].type >= bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].type >= bound1) lines[i].mask |= bit;
          }
        } else if (condition == EQ) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].type == bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].type == bound1) lines[i].mask |= bit;
          }
        } else if (condition == NEQ) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].type != bound1) lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].type != bound1) lines[i].mask |= bit;
          }
        } else if (condition == BETWEEN) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].type >= bound1 && lines[i].type <= bound2)
                lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].type >= bound1 && tris[i].type <= bound2)
                tris[i].mask |= bit;
          }
        }
      }

    // args = list of values

    } else {
      char *ptr;
      int start,stop;

      for (int iarg = 3; iarg < narg; iarg++) {
        if (strchr(arg[iarg],':')) {
          ptr = strchr(arg[iarg],':');
          *ptr = '\0';
          start = input->inumeric(FLERR,arg[iarg]);
          *ptr = ':';
          stop = input->inumeric(FLERR,ptr+1);
        } else {
          start = stop = input->inumeric(FLERR,arg[iarg]);
        }

        // add surf to group if type/id matches value or sequence

        if (category == ID) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].id >= start && lines[i].id <= stop)
                lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].id >= start && tris[i].id <= stop)
                tris[i].mask |= bit;
          }
        } else if (category == TYPE) {
          if (dim == 2) {
            for (i = 0; i < nlocal+nghost; i++)
              if (lines[i].type >= start && lines[i].type <= stop)
                lines[i].mask |= bit;
          } else {
            for (i = 0; i < nlocal+nghost; i++)
              if (tris[i].type >= start && tris[i].type <= stop)
                tris[i].mask |= bit;
          }
        }
      }
    }

  // style = region
  // add surf to group if in region

  } else if (strcmp(arg[2],"region") == 0) {
    if (narg != 5) error->all(FLERR,"Illegal group command");
    int iregion = domain->find_region(arg[3]);
    if (iregion == -1) error->all(FLERR,"Group region ID does not exist");
    Region *region = domain->regions[iregion];

    int rstyle;
    if (strcmp(arg[4],"all") == 0) rstyle = REGION_ALL;
    else if (strcmp(arg[4],"one") == 0) rstyle = REGION_ONE;
    else if (strcmp(arg[4],"center") == 0) rstyle = REGION_CENTER;
    else error->all(FLERR,"Illegal group command");

    if (dim == 2) {
      if (rstyle == REGION_ALL) {
        for (i = 0; i < nlocal+nghost; i++) {
          flag = 1;
          if (!region->match(lines[i].p1)) flag = 0;
          if (!region->match(lines[i].p2)) flag = 0;
          if (flag) lines[i].mask |= bit;
        }
      } else if (rstyle == REGION_ONE) {
        for (i = 0; i < nlocal+nghost; i++) {
          flag = 0;
          if (region->match(lines[i].p1)) flag = 1;
          if (region->match(lines[i].p2)) flag = 1;
          if (flag) lines[i].mask |= bit;
        }
      } else if (rstyle == REGION_CENTER) {
        for (i = 0; i < nlocal+nghost; i++) {
          x[0] = 0.5 * (lines[i].p1[0] + lines[i].p2[0]);
          x[1] = 0.5 * (lines[i].p1[1] + lines[i].p2[1]);
          x[2] = 0.0;
          if (region->match(x)) lines[i].mask |= bit;
        }
      }

    } else if (dim == 3) {
      if (rstyle == REGION_ALL) {
        for (i = 0; i < nlocal+nghost; i++) {
          flag = 1;
          if (!region->match(tris[i].p1)) flag = 0;
          if (!region->match(tris[i].p2)) flag = 0;
          if (!region->match(tris[i].p3)) flag = 0;
          if (flag) tris[i].mask |= bit;
        }
      } else if (rstyle == REGION_ONE) {
        for (i = 0; i < nlocal+nghost; i++) {
          flag = 0;
          if (region->match(tris[i].p1)) flag = 1;
          if (region->match(tris[i].p2)) flag = 1;
          if (region->match(tris[i].p3)) flag = 1;
          if (flag) tris[i].mask |= bit;
        }
      } else if (rstyle == REGION_CENTER) {
        for (i = 0; i < nlocal+nghost; i++) {
          x[0] = (tris[i].p1[0] + tris[i].p2[0] + tris[i].p3[0]) / 3.0;
          x[1] = (tris[i].p1[1] + tris[i].p2[1] + tris[i].p3[1]) / 3.0;
          x[2] = (tris[i].p1[2] + tris[i].p2[2] + tris[i].p3[2]) / 3.0;
          if (region->match(x)) tris[i].mask |= bit;
        }
      }
    }

  // style = subtract

  } else if (strcmp(arg[2],"subtract") == 0) {
    if (narg < 5) error->all(FLERR,"Illegal group command");

    int length = narg-3;
    int *list = new int[length];

    int jgroup;
    for (int iarg = 3; iarg < narg; iarg++) {
      jgroup = find_group(arg[iarg]);
      if (jgroup == -1) error->all(FLERR,"Group ID does not exist");
      list[iarg-3] = jgroup;
    }

    // add to group if in 1st group in list

    int otherbit = bitmask[list[0]];

    if (dim == 2) {
      for (i = 0; i < nlocal+nghost; i++)
        if (lines[i].mask & otherbit) lines[i].mask |= bit;
    } else {
      for (i = 0; i < nlocal+nghost; i++)
        if (tris[i].mask & otherbit) tris[i].mask |= bit;
    }

    // remove surfs if they are in any of the other groups
    // AND with inverse mask removes the surf from group

    int inverse = inversemask[igroup];

    for (int ilist = 1; ilist < length; ilist++) {
      otherbit = bitmask[list[ilist]];
      if (dim == 2) {
        for (i = 0; i < nlocal+nghost; i++)
          if (lines[i].mask & otherbit) lines[i].mask &= inverse;
      } else {
        for (i = 0; i < nlocal+nghost; i++)
          if (tris[i].mask & otherbit) tris[i].mask &= inverse;
      }
    }

    delete [] list;

  // style = union

  } else if (strcmp(arg[2],"union") == 0) {
    if (narg < 4) error->all(FLERR,"Illegal group command");

    int length = narg-3;
    int *list = new int[length];

    int jgroup;
    for (int iarg = 3; iarg < narg; iarg++) {
      jgroup = find_group(arg[iarg]);
      if (jgroup == -1) error->all(FLERR,"Group ID does not exist");
      list[iarg-3] = jgroup;
    }

    // add to group if in any other group in list

    int otherbit;

    for (int ilist = 0; ilist < length; ilist++) {
      otherbit = bitmask[list[ilist]];
      if (dim == 2) {
        for (i = 0; i < nlocal+nghost; i++)
          if (lines[i].mask & otherbit) lines[i].mask |= bit;
      } else {
        for (i = 0; i < nlocal+nghost; i++)
          if (tris[i].mask & otherbit) tris[i].mask |= bit;
      }
    }

    delete [] list;

  // style = intersect

  } else if (strcmp(arg[2],"intersect") == 0) {
    if (narg < 5) error->all(FLERR,"Illegal group command");

    int length = narg-3;
    int *list = new int[length];

    int jgroup;
    for (int iarg = 3; iarg < narg; iarg++) {
      jgroup = find_group(arg[iarg]);
      if (jgroup == -1) error->all(FLERR,"Group ID does not exist");
      list[iarg-3] = jgroup;
    }

    // add to group if in all groups in list

    int otherbit,ok,ilist;

    if (dim == 2) {
      for (i = 0; i < nlocal+nghost; i++) {
        ok = 1;
        for (ilist = 0; ilist < length; ilist++) {
          otherbit = bitmask[list[ilist]];
          if ((lines[i].mask & otherbit) == 0) ok = 0;
        }
        if (ok) lines[i].mask |= bit;
      }
    } else {
      for (i = 0; i < nlocal+nghost; i++) {
        ok = 1;
        for (ilist = 0; ilist < length; ilist++) {
          otherbit = bitmask[list[ilist]];
          if ((tris[i].mask & otherbit) == 0) ok = 0;
        }
        if (ok) tris[i].mask |= bit;
      }
    }

    delete [] list;

  // style = clear
  // remove all surfs from group

  } else if (strcmp(arg[2],"clear") == 0) {
    if (igroup == 0) error->all(FLERR,"Cannot clear group all");
    int inversebits = inversemask[igroup];

    if (dim == 2) {
      for (i = 0; i < nlocal+nghost; i++) lines[i].mask &= inversebits;
    } else {
      for (i = 0; i < nlocal+nghost; i++) tris[i].mask &= inversebits;
    }
  }

  // print stats for changed group

  bigint n = 0;
  if (dim == 2) {
    for (i = 0; i < nlocal; i++)
      if (lines[i].mask & bit) n++;
  } else {
    for (i = 0; i < nlocal; i++)
      if (tris[i].mask & bit) n++;
  }

  bigint nall;
  if (distributed) MPI_Allreduce(&n,&nall,1,MPI_SPARTA_BIGINT,MPI_SUM,world);
  else nall = n;

  if (comm->me == 0) {
    if (screen)
      fprintf(screen,BIGINT_FORMAT " surfaces in group %s\n",
              nall,gnames[igroup]);
    if (logfile)
      fprintf(logfile,BIGINT_FORMAT " surfaces in group %s\n",
              nall,gnames[igroup]);
  }
}

/* ----------------------------------------------------------------------
   add a new surface group ID, assumed to be unique
------------------------------------------------------------------------- */

int Surf::add_group(const char *id)
{
  if (ngroup == MAXGROUP)
    error->all(FLERR,"Cannot have more than 32 surface groups");

  int n = strlen(id) + 1;
  gnames[ngroup] = new char[n];
  strcpy(gnames[ngroup],id);

  for (int i = 0; i < n-1; i++)
    if (!isalnum(id[i]) && id[i] != '_')
      error->all(FLERR,"Group ID must be alphanumeric or "
                 "underscore characters");

  ngroup++;
  return ngroup-1;
}

/* ----------------------------------------------------------------------
   find a surface group ID
   return index of group or -1 if not found
------------------------------------------------------------------------- */

int Surf::find_group(const char *id)
{
  int igroup;
  for (igroup = 0; igroup < ngroup; igroup++)
    if (strcmp(id,gnames[igroup]) == 0) break;
  if (igroup == ngroup) return -1;
  return igroup;
}

/* ----------------------------------------------------------------------
   compress owned explicit distributed surfs to account for deleted grid cells
     either due to load-balancing migration or grid adapt coarsening
   called from Comm::migrate_cells() and AdaptGrid::coarsen()
     AFTER grid cells are compressed
   discard nlocal surfs that are no longer referenced by owned grid cells
   use hash to store referenced surfs
   only called for explicit distributed surfs
------------------------------------------------------------------------- */

void Surf::compress_explicit()
{
  int i,m,ns;
  surfint *csurfs;

  int dim = domain->dimension;

  // keep = 1 if a local surf is referenced by a compressed local grid cell

  int *keep;
  memory->create(keep,nlocal,"surf:keep");
  for (i = 0; i < nlocal; i++) keep[i] = 0;

  // convert grid cell csurfs to surf IDs so can reset after surf compression
  // skip cells with no surfs or sub-cells

  Grid::ChildCell *cells = grid->cells;
  int nglocal = grid->nlocal;

  for (i = 0; i < nglocal; i++) {
    if (!cells[i].nsurf) continue;
    if (cells[i].nsplit <= 0) continue;
    csurfs = cells[i].csurfs;
    ns = cells[i].nsurf;
    if (dim == 2) {
      for (m = 0; m < ns; m++) {
        keep[csurfs[m]] = 1;
        csurfs[m] = lines[csurfs[m]].id;
      }
    } else {
      for (m = 0; m < ns; m++) {
        keep[csurfs[m]] = 1;
        csurfs[m] = tris[csurfs[m]].id;
      }
    }
  }

  // compress nlocal surfs based on keep flags

  m = 0;
  while (i < nlocal) {
    if (!keep[i]) {
      if (dim == 2) memcpy(&lines[i],&lines[nlocal-1],sizeof(Line));
      else memcpy(&tris[i],&tris[nlocal-1],sizeof(Tri));
      keep[i] = keep[nlocal-1];
      nlocal--;
    } else i++;
  }

  memory->destroy(keep);

  // reset grid cell csurfs IDs back to local surf indices
  // hash compressed surf list, then clear hash
  // skip cells with no surfs or sub-cells

  rehash();

  for (i = 0; i < nglocal; i++) {
    if (!cells[i].nsurf) continue;
    if (cells[i].nsplit <= 0) continue;
    csurfs = cells[i].csurfs;
    ns = cells[i].nsurf;
    for (m = 0; m < ns; m++) csurfs[m] = (*hash)[csurfs[m]];
  }

  hash->clear();
  hashfilled = 0;
}

/* ----------------------------------------------------------------------
   compress owned implicit surfs to account for migrating grid cells
   called from Comm::migrate_cells() BEFORE grid cells are compressed
   migrating grid cells are ones with proc != me
   reset csurfs indices for kept cells
   only called for implicit surfs
------------------------------------------------------------------------- */

void Surf::compress_implicit()
{
  int j,ns,icell;
  cellint cellID;
  surfint *csurfs;

  if (!grid->hashfilled) grid->rehash();

  Grid::ChildCell *cells = grid->cells;
  Grid::MyHash *ghash = grid->hash;
  int me = comm->me;
  int n = 0;

  if (domain->dimension == 2) {
    for (int i = 0; i < nlocal; i++) {
      icell = (*ghash)[lines[i].id];
      if (cells[icell].proc != me) continue;
      if (i != n) {
        // compress my surf list
        memcpy(&lines[n],&lines[i],sizeof(Line));
        // reset matching csurfs index in grid cell from i to n
        csurfs = cells[icell].csurfs;
        ns = cells[icell].nsurf;
        for (j = 0; j < ns; j++)
          if (csurfs[j] == i) {
            csurfs[j] = n;
            break;
          }
      }
      n++;
    }

  } else {
    for (int i = 0; i < nlocal; i++) {
      icell = (*ghash)[tris[i].id];
      if (cells[icell].proc != me) continue;
      if (i != n) {
        // compress my surf list
        memcpy(&tris[n],&tris[i],sizeof(Tri));
        // reset matching csurfs index in grid cell from i to n
        csurfs = cells[icell].csurfs;
        ns = cells[icell].nsurf;
        for (j = 0; j < ns; j++)
          if (csurfs[j] == i) {
            csurfs[j] = n;
            break;
          }
      }
      n++;
    }
  }

  nlocal = n;
}

/* ----------------------------------------------------------------------
   comm of tallies across all procs
   nrow = # of tally entries in input vector
   tally2surf = surf index of each entry in input vector
   in = input vector of tallies
   instride = stride between entries in input vector
   return out = summed tallies for explicit surfs I own
------------------------------------------------------------------------- */

void Surf::collate_vector(int nrow, surfint *tally2surf,
                          double *in, int instride, double *out)
{
  // collate version depends on tally_comm setting

  if (tally_comm == TALLYAUTO) {
    if (nprocs > nsurf)
      collate_vector_reduce(nrow,tally2surf,in,instride,out);
    else collate_vector_rendezvous(nrow,tally2surf,in,instride,out);
  } else if (tally_comm == TALLYREDUCE) {
    collate_vector_reduce(nrow,tally2surf,in,instride,out);
  } else if (tally_comm == TALLYRVOUS) {
    collate_vector_rendezvous(nrow,tally2surf,in,instride,out);
  }
}

/* ----------------------------------------------------------------------
   allreduce version of collate
------------------------------------------------------------------------- */

void Surf::collate_vector_reduce(int nrow, surfint *tally2surf,
                                 double *in, int instride, double *out)
{
  int i,j,m;

  if (nsurf > MAXSMALLINT)
    error->all(FLERR,"Two many surfs to tally reduce - "
               "use global surf/comm auto or rvous");

  int nglobal = nsurf;

  double *one,*all;
  memory->create(one,nglobal,"surf:one");
  memory->create(all,nglobal,"surf:all");

  // zero all values and add in values I accumulated

  memset(one,0,nglobal*sizeof(double));

  Surf::Line *lines = surf->lines;
  Surf::Tri *tris = surf->tris;
  int dim = domain->dimension;
  surfint id;

  j = 0;
  for (i = 0; i < nrow; i++) {
    m = (int) tally2surf[i] - 1;
    one[m] = in[j];
    j += instride;
  }

  // global allreduce

  MPI_Allreduce(one,all,nglobal,MPI_DOUBLE,MPI_SUM,world);

  // out = only surfs I own

  m = 0;
  for (i = me; i < nglobal; i += nprocs)
    out[m++] = all[i];

  // NOTE: could persist these for multiple invocations

  memory->destroy(one);
  memory->destroy(all);
}

/* ----------------------------------------------------------------------
   rendezvous version of collate
------------------------------------------------------------------------- */

void Surf::collate_vector_rendezvous(int nrow, surfint *tally2surf,
                                     double *in, int instride, double *out)
{
  // allocate memory for rvous input

  int *proclist;
  memory->create(proclist,nrow,"surf:proclist");
  InRvousVec *in_rvous =
    (InRvousVec *) memory->smalloc((bigint) nrow*sizeof(InRvousVec),
                                   "surf:in_rvous");

  // create rvous inputs
  // proclist = owner of each surf
  // logic of (id-1) % nprocs sends
  //   surf IDs 1,11,21,etc on 10 procs to proc 0

  Surf::Line *lines = surf->lines;
  Surf::Tri *tris = surf->tris;
  int dim = domain->dimension;

  surfint id;

  int m = 0;
  for (int i = 0; i < nrow; i++) {
    id = tally2surf[i];
    proclist[i] = (id-1) % nprocs;
    in_rvous[i].id = id;
    in_rvous[i].value = in[m];
    m += instride;
  }

  // perform rendezvous operation
  // each proc owns subset of surfs
  // receives all tally contributions to surfs it owns

  out_rvous = out;

  char *buf;
  int nout = comm->rendezvous(1,nrow,(char *) in_rvous,sizeof(InRvousVec),
                              0,proclist,rendezvous_vector,
                              0,buf,0,(void *) this);

  memory->destroy(proclist);
  memory->destroy(in_rvous);
}

/* ----------------------------------------------------------------------
   callback from rendezvous operation
   process tallies for surfs assigned to me
   inbuf = list of N Inbuf datums
   no outbuf
------------------------------------------------------------------------- */

int Surf::rendezvous_vector(int n, char *inbuf, int &flag, int *&proclist,
                            char *&outbuf, void *ptr)
{
  Surf *sptr = (Surf *) ptr;
  Memory *memory = sptr->memory;
  int nown = sptr->nown;
  double *out = sptr->out_rvous;
  int nprocs = sptr->comm->nprocs;
  int me = sptr->comm->me;

  // zero my owned surf values

  for (int i = 0; i < nown; i++) out[i] = 0.0;

  // accumulate per-surf values from different procs to my owned surfs
  // logic of (id-1-me) / nprocs maps
  //   surf IDs [1,11,21,...] on 10 procs to [0,1,2,...] on proc 0

  Surf::InRvousVec *in_rvous = (Surf::InRvousVec *) inbuf;

  int m;
  for (int i = 0; i < n; i++) {
    m = (in_rvous[i].id-1-me) / nprocs;
    out[m] += in_rvous[i].value;
  }

  // flag = 0: no second comm needed in rendezvous

  flag = 0;
  return 0;
}

/* ----------------------------------------------------------------------
   comm of tallies across all procs
   nrow,ncol = # of entries and columns in input array
   tally2surf = global surf index of each entry in input array
   in = input array of tallies
   return out = summed tallies for explicit surfs I own
------------------------------------------------------------------------- */

void Surf::collate_array(int nrow, int ncol, surfint *tally2surf,
                         double **in, double **out)
{
  // collate version depends on tally_comm setting

  if (tally_comm == TALLYAUTO) {
    if (nprocs > nsurf)
      collate_array_reduce(nrow,ncol,tally2surf,in,out);
    else collate_array_rendezvous(nrow,ncol,tally2surf,in,out);
  } else if (tally_comm == TALLYREDUCE) {
    collate_array_reduce(nrow,ncol,tally2surf,in,out);
  } else if (tally_comm == TALLYRVOUS) {
    collate_array_rendezvous(nrow,ncol,tally2surf,in,out);
  }
}

/* ----------------------------------------------------------------------
   allreduce version of collate
------------------------------------------------------------------------- */

void Surf::collate_array_reduce(int nrow, int ncol, surfint *tally2surf,
                                double **in, double **out)
{
  int i,j,m;

  bigint ntotal = (bigint) nsurf * ncol;

  if (ntotal > MAXSMALLINT)
    error->all(FLERR,"Two many surfs to tally reduce - "
               "use global surf/comm auto or rvous");

  int nglobal = nsurf;

  double **one,**all;
  memory->create(one,nglobal,ncol,"surf:one");
  memory->create(all,nglobal,ncol,"surf:all");

  // zero all values and set values I accumulated

  memset(&one[0][0],0,nglobal*ncol*sizeof(double));

  Surf::Line *lines = surf->lines;
  Surf::Tri *tris = surf->tris;
  int dim = domain->dimension;

  for (i = 0; i < nrow; i++) {
    m = (int) tally2surf[i] - 1;
    for (j = 0; j < ncol; j++)
      one[m][j] = in[i][j];
  }

  // global allreduce

  MPI_Allreduce(&one[0][0],&all[0][0],ntotal,MPI_DOUBLE,MPI_SUM,world);

  // out = only surfs I own

  m = 0;
  for (i = me; i < nglobal; i += nprocs) {
    for (j = 0; j < ncol; j++) out[m][j] = all[i][j];
    m++;
  }

  // NOTE: could persist these for multiple invocations

  memory->destroy(one);
  memory->destroy(all);
}

/* ----------------------------------------------------------------------
   rendezvous version of collate
------------------------------------------------------------------------- */

void Surf::collate_array_rendezvous(int nrow, int ncol, surfint *tally2surf,
                                    double **in, double **out)
{
  int i,j,m;

  // allocate memory for rvous input

  int *proclist;
  memory->create(proclist,nrow,"surf:proclist");
  double *in_rvous = (double *)     // worry about overflow
    memory->smalloc(nrow*(ncol+1)*sizeof(double*),"surf:in_rvous");

  // create rvous inputs
  // proclist = owner of each surf
  // logic of (id-1) % nprocs sends
  //   surf IDs 1,11,21,etc on 10 procs to proc 0

  Surf::Line *lines = surf->lines;
  Surf::Tri *tris = surf->tris;
  int dim = domain->dimension;
  surfint id;

  m = 0;
  for (int i = 0; i < nrow; i++) {
    id = tally2surf[i];
    proclist[i] = (id-1) % nprocs;
    in_rvous[m++] = ubuf(id).d;
    for (j = 0; j < ncol; j++)
      in_rvous[m++] = in[i][j];
  }

  // perform rendezvous operation
  // each proc owns subset of surfs
  // receives all tally contributions to surfs it owns

  ncol_rvous = ncol;
  if (out == NULL) out_rvous = NULL;
  else out_rvous = &out[0][0];
  int size = (ncol+1) * sizeof(double);

  char *buf;
  int nout = comm->rendezvous(1,nrow,(char *) in_rvous,size,
                              0,proclist,rendezvous_array,
                              0,buf,0,(void *) this);

  memory->destroy(proclist);
  memory->sfree(in_rvous);
}

/* ----------------------------------------------------------------------
   callback from rendezvous operation
   process tallies for surfs assigned to me
   inbuf = list of N Inbuf datums
   no outbuf
------------------------------------------------------------------------- */

int Surf::rendezvous_array(int n, char *inbuf,
                           int &flag, int *&proclist, char *&outbuf,
                           void *ptr)
{
  int i,j,k,m;

  Surf *sptr = (Surf *) ptr;
  Memory *memory = sptr->memory;
  int nown = sptr->nown;
  int ncol = sptr->ncol_rvous;
  double *out = sptr->out_rvous;
  int nprocs = sptr->comm->nprocs;
  int me = sptr->comm->me;

  // zero my owned surf values
  // NOTE: is this needed if caller zeroes ?

  int ntotal = nown*ncol;
  for (m = 0; m < ntotal; m++) out[m] = 0.0;

  // accumulate per-surf values from different procs to my owned surfs
  // logic of (id-1-me) / nprocs maps
  //   surf IDs [1,11,21,...] on 10 procs to [0,1,2,...] on proc 0

  double *in_rvous = (double *) inbuf;
  surfint id;

  m = 0;
  for (int i = 0; i < n; i++) {
    id = (surfint) ubuf(in_rvous[m++]).i;
    k = (id-1-me) / nprocs * ncol;
    for (j = 0; j < ncol; j++)
      out[k++] += in_rvous[m++];
  }

  // flag = 0: no second comm needed in rendezvous

  flag = 0;
  return 0;
}

/* ----------------------------------------------------------------------
   comm of tallies across all procs
   called from compute isurf/grid and fix ave/grid
     for implicit surf tallies by grid cell
   nrow = # of tallies
   tally2surf = surf ID for each tally (same as cell ID)
   in = vectir of tally values
   return out = summed tallies for grid cells I own
   done via rendezvous algorithm
------------------------------------------------------------------------- */

void Surf::collate_vector_implicit(int nrow, surfint *tally2surf,
                                   double *in, double *out)
{
  int i,j,m,icell;
  cellint cellID;

  int me = comm->me;
  int nprocs = comm->nprocs;

  // create a grid cell hash for only my owned cells

  Grid::ChildCell *cells = grid->cells;
  int nglocal = grid->nlocal;

  MyCellHash hash;

  for (int icell = 0; icell < nglocal; icell++) {
    if (cells[icell].nsplit <= 0) continue;
    hash[cells[icell].id] = icell;
  }

  // for implicit surfs, tally2surf stores cellIDs

  cellint *tally2cell = (cellint *) tally2surf;

  // if I own tally grid cell, sum tallies to out directly
  // else nsend = # of tallies to contribute to rendezvous

  int nsend = 0;
  for (i = 0; i < nrow; i++) {
    if (hash.find(tally2cell[i]) == hash.end()) nsend++;
    else {
      icell = hash[tally2cell[i]];
      out[icell] += in[i];
    }
  }

  // done if just one proc

  if (nprocs == 1) return;

  // ncell = # of owned grid cells with implicit surfs, excluding sub cells
  // NOTE: could limit to cell group of caller

  int ncell = 0;
  for (int icell = 0; icell < nglocal; icell++) {
    if (cells[icell].nsurf <= 0) continue;
    if (cells[icell].nsplit <= 0) continue;
    ncell++;
  }

  // allocate memory for rvous input
  // ncount = ncell + nsend
  // 3 doubles for each input = proc, cellID, tally

  int ncount = ncell + nsend;

  int *proclist;
  double *in_rvous;
  memory->create(proclist,ncount,"surf:proclist");
  memory->create(in_rvous,3*ncount,"surf:in_rvous");

  // create rvous inputs
  // owning proc for each datum = random hash of cellID
  // flavor 1: one per ncell with proc and cellID, no tally
  // flavor 2: one per nsend with proc = -1, cellID, one tally

  ncount = m = 0;

  for (int icell = 0; icell < nglocal; icell++) {
    if (cells[icell].nsurf <= 0) continue;
    if (cells[icell].nsplit <= 0) continue;
    proclist[ncount] = hashlittle(&cells[icell].id,sizeof(cellint),0) % nprocs;
    in_rvous[m++] = me;
    in_rvous[m++] = cells[icell].id;    // NOTE: should use ubuf
    in_rvous[m++] = 0.0;
    ncount++;
  }

  for (i = 0; i < nrow; i++) {
    if (hash.find(tally2cell[i]) == hash.end()) {
      proclist[ncount] = hashlittle(&tally2cell[i],sizeof(cellint),0) % nprocs;
      in_rvous[m++] = -1;
      in_rvous[m++] = tally2cell[i];    // NOTE: should use ubuf
      in_rvous[m++] = in[i];
      ncount++;
    }
  }

  // perform rendezvous operation

  ncol_rvous = 1;
  char *buf;
  int nout = comm->rendezvous(1,ncount,(char *) in_rvous,3*sizeof(double),
                              0,proclist,rendezvous_implicit,
                              0,buf,2*sizeof(double),(void *) this);
  double *out_rvous = (double *) buf;

  memory->destroy(proclist);
  memory->destroy(in_rvous);

  // sum tallies returned for grid cells I own into out

  m = 0;
  for (i = 0; i < nout; i++) {
    cellID = out_rvous[m++];      // NOTE: should use ubuf
    icell = hash[cellID];
    out[icell] += out_rvous[m++];
  }

  // clean-up

  memory->destroy(out_rvous);
}

/* ----------------------------------------------------------------------
   comm of tallies across all procs
   called from compute isurf/grid and fix ave/grid
     for implicit surf tallies by grid cell
   nrow = # of tallies
   ncol = # of values per tally
   tally2surf = surf ID for each tally (same as cell ID)
   in = array of tally values, nrow by ncol
   return out = summed tallies for grid cells I own, nlocal by ncol
   done via rendezvous algorithm
------------------------------------------------------------------------- */

void Surf::collate_array_implicit(int nrow, int ncol, surfint *tally2surf,
                                  double **in, double **out)
{
  int i,j,m,icell;
  cellint cellID;

  int me = comm->me;
  int nprocs = comm->nprocs;

  // create a grid cell hash for only my owned cells

  Grid::ChildCell *cells = grid->cells;
  int nglocal = grid->nlocal;

  MyCellHash hash;

  for (int icell = 0; icell < nglocal; icell++) {
    if (cells[icell].nsplit <= 0) continue;
    hash[cells[icell].id] = icell;
  }

  // for implicit surfs, tally2surf stores cellIDs

  cellint *tally2cell = (cellint *) tally2surf;

  // if I own tally grid cell, sum tallies to out directly
  // else nsend = # of tallies to contribute to rendezvous

  int nsend = 0;
  for (i = 0; i < nrow; i++) {
    if (hash.find(tally2cell[i]) == hash.end()) nsend++;
    else {
      icell = hash[tally2cell[i]];
      for (j = 0; j < ncol; j++)
        out[icell][j] += in[i][j];
    }
  }

  // done if just one proc

  if (nprocs == 1) return;

  // ncell = # of owned grid cells with implicit surfs, excluding sub cells
  // NOTE: could limit to cell group of caller

  int ncell = 0;
  for (int icell = 0; icell < nglocal; icell++) {
    if (cells[icell].nsurf <= 0) continue;
    if (cells[icell].nsplit <= 0) continue;
    ncell++;
  }

  // allocate memory for rvous input
  // ncount = ncell + nsend
  // ncol+2 doubles for each input = proc, cellID, ncol values

  int ncount = ncell + nsend;

  int *proclist;
  double *in_rvous;
  memory->create(proclist,ncount,"surf:proclist");
  memory->create(in_rvous,ncount*(ncol+2),"surf:in_rvous");

  // create rvous inputs
  // owning proc for each datum = random hash of cellID
  // flavor 1: one per ncell with proc and cellID, no tallies
  // flavor 2: one per nsend with proc = -1, cellID, tallies

  ncount = m = 0;

  for (int icell = 0; icell < nglocal; icell++) {
    if (cells[icell].nsurf <= 0) continue;
    if (cells[icell].nsplit <= 0) continue;
    proclist[ncount] = hashlittle(&cells[icell].id,sizeof(cellint),0) % nprocs;
    in_rvous[m++] = me;
    in_rvous[m++] = cells[icell].id;    // NOTE: should use ubuf
    for (j = 0; j < ncol; j++)
      in_rvous[m++] = 0.0;
    ncount++;
  }

  for (i = 0; i < nrow; i++) {
    if (hash.find(tally2cell[i]) == hash.end()) {
      proclist[ncount] = hashlittle(&tally2cell[i],sizeof(cellint),0) % nprocs;
      in_rvous[m++] = -1;
      in_rvous[m++] = tally2cell[i];    // NOTE: should use ubuf
      for (j = 0; j < ncol; j++)
        in_rvous[m++] = in[i][j];
      ncount++;
    }
  }

  // perform rendezvous operation

  ncol_rvous = ncol;
  char *buf;
  int nout = comm->rendezvous(1,ncount,(char *) in_rvous,
                              (ncol+2)*sizeof(double),
                              0,proclist,rendezvous_implicit,
                              0,buf,(ncol+1)*sizeof(double),(void *) this);
  double *out_rvous = (double *) buf;

  memory->destroy(proclist);
  memory->destroy(in_rvous);

  // sum tallies returned for grid cells I own into out

  m = 0;
  for (i = 0; i < nout; i++) {
    cellID = out_rvous[m++];      // NOTE: should use ubuf
    icell = hash[cellID] - 1;     // subtract one for child cell index
    for (j = 0; j < ncol; j++)
      out[icell][j] += out_rvous[m++];
  }

  // clean-up

  memory->destroy(out_rvous);
}

/* ----------------------------------------------------------------------
   callback from rendezvous operation
   create summed tallies for each grid cell assigned to me
   inbuf = list of N input datums
   send cellID + Ncol values back to owning proc of each grid cell
------------------------------------------------------------------------- */

int Surf::rendezvous_implicit(int n, char *inbuf,
                              int &flag, int *&proclist, char *&outbuf, void *ptr)
{
  int i,j,k,m,proc,iout;
  cellint cellID;

  Surf *sptr = (Surf *) ptr;
  Memory *memory = sptr->memory;
  int ncol = sptr->ncol_rvous;

  // scan inbuf for (proc,cellID) entries
  // create phash so can lookup the proc for each cellID

  double *in_rvous = (double *) inbuf;
  MyCellHash phash;

  m = 0;
  for (i = 0; i < n; i++) {
    proc = static_cast<int> (in_rvous[m++]);
    cellID = static_cast<cellint> (in_rvous[m++]);
    if (proc >= 0 && phash.find(cellID) == phash.end()) phash[cellID] = proc;
    m += ncol;
  }

  // allocate proclist & outbuf, based on size of max-size of phash

  int nmax = phash.size();
  memory->create(proclist,nmax,"surf:proclist");
  double *out;
  memory->create(out,nmax*(ncol+1),"surf:out");

  // scan inbuf for (cellID,tallies) entries
  // create a 2nd hash so can lookup the outbuf entry for each cellID
  // create proclist and outbuf with summed tallies for every cellID

  MyCellHash ohash;

  int nout = 0;
  k = m = 0;

  for (i = 0; i < n; i++) {
    proc = static_cast<int> (in_rvous[m++]);
    cellID = static_cast<cellint> (in_rvous[m++]);
    if (proc >= 0) {
      m += ncol;                         // skip entries with novalues
      continue;
    }
    if (ohash.find(cellID) == phash.end()) {
      ohash[cellID] = nout;              // add a new set of out values
      proclist[nout] = phash[cellID];
      out[k++] = cellID;
      for (j = 0; j < ncol; j++)
        out[k++] = in_rvous[m++];
      nout++;
    } else {
      iout = ohash[cellID] * (ncol+1);   // offset into existing out values
      iout++;                            // skip cellID;
      for (j = 0; j < ncol; j++)
        out[iout++] += in_rvous[m++];    // sum to existing values
    }
  }

  // flag = 2: new outbuf

  flag = 2;
  outbuf = (char *) out;
  return nout;
}

/* ----------------------------------------------------------------------
   redistribute newly created distributed lines to owing procs
   nold = original nown value before new surfs were read in
   nown = current nown value that includes my new surfs to redistribute
   nnew = nown value after new surfs from all procs are assigned to me
   called by ReadSurf:clip() after proc creates new surfs via clipping
   only called for distributed surfs
------------------------------------------------------------------------- */

void Surf::redistribute_lines_clip(int nold, int nnew)
{
  // allocate memory for rvous input

  int nsend = nown - nold;

  int *proclist;
  memory->create(proclist,nsend,"surf:proclist");
  Line *in_rvous = (Line *) memory->smalloc(nsend*sizeof(Line),"surf:in_rvous");

  // create rvous inputs
  // proclist = owner of each surf = (id-1) % nprocs

  surfint id;

  int i = nold;
  for (int m = 0; m < nsend; m++) {
    id = mylines[i].id;
    proclist[m] = (id-1) % nprocs;
    memcpy(&in_rvous[m],&mylines[i],sizeof(Line));
    i++;
  }

  // insure mylines is allocated sufficient for new lines
  // reset nown to new value after rendezvous

  if (nnew > maxown) {
    int old = maxown;
    maxown = nnew;
    grow_own(old);
  }
  nown = nnew;

  // perform rendezvous operation
  // each proc owns subset of new surfs
  // receives them from other procs

  char *buf;
  int nout = comm->rendezvous(1,nsend,(char *) in_rvous,sizeof(Line),
                              0,proclist,rendezvous_lines,
                              0,buf,0,(void *) this);

  memory->destroy(proclist);
  memory->sfree(in_rvous);
}

/* ----------------------------------------------------------------------
   redistribute newly created distributed lines to owing procs
   nnew = nown value after new surfs from all procs are assigned to me
   called by ReadSurf:read_multiple()
   only called for distributed surfs
------------------------------------------------------------------------- */

void Surf::redistribute_lines_temporary(int nnew)
{
  // allocate memory for rvous input

  int nsend = ntmp;

  int *proclist;
  memory->create(proclist,nsend,"surf:proclist");
  Line *in_rvous = (Line *) memory->smalloc(nsend*sizeof(Line),"surf:in_rvous");

  // create rvous inputs
  // proclist = owner of each surf = (id-1) % nprocs

  surfint id;

  for (int i = 0; i < nsend; i++) {
    id = tmplines[i].id;
    proclist[i] = (id-1) % nprocs;
    memcpy(&in_rvous[i],&tmplines[i],sizeof(Line));
  }

  // insure mylines is allocated sufficient for new lines
  // reset nown to new value after rendezvous

  if (nnew > maxown) {
    int old = maxown;
    maxown = nnew;
    grow_own(old);
  }
  nown = nnew;

  // perform rendezvous operation
  // each proc owns subset of new surfs
  // receives them from other procs

  char *buf;
  int nout = comm->rendezvous(1,nsend,(char *) in_rvous,sizeof(Line),
                              0,proclist,rendezvous_lines,
                              0,buf,0,(void *) this);

  memory->destroy(proclist);
  memory->sfree(in_rvous);
}

/* ----------------------------------------------------------------------
   callback from rendezvous operation
   store received surfs assigned to me in correct location in mylines
   inbuf = list of N Inbuf datums
   no outbuf
------------------------------------------------------------------------- */

int Surf::rendezvous_lines(int n, char *inbuf,
                           int &flag, int *&proclist, char *&outbuf,
                           void *ptr)
{
  int i,j,k,m;

  Surf *sptr = (Surf *) ptr;
  Line *lines = sptr->mylines;
  int nprocs = sptr->comm->nprocs;
  int me = sptr->comm->me;

  // zero my owned surf values

  Line *in_rvous = (Line *) inbuf;
  surfint id;

  for (int i = 0; i < n; i++) {
    id = in_rvous[i].id;
    m = (id-1-me) / nprocs;
    memcpy(&lines[m],&in_rvous[i],sizeof(Line));
  }

  // flag = 0: no second comm needed in rendezvous

  flag = 0;
  return 0;
}

/* ----------------------------------------------------------------------
   redistribute newly created distributed tris to owing procs
   nold = original nown value before new surfs were read in
   nown = current nown value that includes my new surfs to redistribute
   nnew = nown value after new surfs from all procs are assigned to me
   old = starting index that skips previously distributed surfs
   called by ReadSurf:clip() after proc create new surfs via clipping
   only called for distributed surfs
------------------------------------------------------------------------- */

void Surf::redistribute_tris_clip(int nold, int nnew)
{
  // allocate memory for rvous input

  int nsend = nown - nold;

  int *proclist;
  memory->create(proclist,nsend,"surf:proclist");
  Tri *in_rvous = (Tri *) memory->smalloc(nsend*sizeof(Tri),"surf:in_rvous");

  // create rvous inputs
  // proclist = owner of each surf = (id-1) % nprocs

  surfint id;

  int i = nold;
  for (int m = 0; m < nsend; m++) {
    id = mytris[i].id;
    proclist[m] = (id-1) % nprocs;
    memcpy(&in_rvous[m],&mytris[i],sizeof(Tri));
    i++;
  }

  // insure mytris is allocated sufficient for new tris
  // reset nown to new value after rendezvous

  if (nnew > maxown) {
    int old = maxown;
    maxown = nnew;
    grow_own(old);
  }
  nown = nnew;

  // perform rendezvous operation
  // each proc owns subset of new surfs
  // receives them from other procs

  char *buf;
  int nout = comm->rendezvous(1,nsend,(char *) in_rvous,sizeof(Tri),
                              0,proclist,rendezvous_tris,
                              0,buf,0,(void *) this);

  memory->destroy(proclist);
  memory->sfree(in_rvous);
}

/* ----------------------------------------------------------------------
   redistribute newly created distributed tris to owing procs
   nnew = nown value after new surfs from all procs are assigned to me
   called by ReadSurf:read_multiple()
   only called for distributed surfs
------------------------------------------------------------------------- */

void Surf::redistribute_tris_temporary(int nnew)
{
  // allocate memory for rvous input

  int nsend = ntmp;

  int *proclist;
  memory->create(proclist,nsend,"surf:proclist");
  Tri *in_rvous = (Tri *) memory->smalloc(nsend*sizeof(Tri),"surf:in_rvous");

  // create rvous inputs
  // proclist = owner of each surf = (id-1) % nprocs

  surfint id;

  for (int i = 0; i < nsend; i++) {
    id = tmptris[i].id;
    proclist[i] = (id-1) % nprocs;
    memcpy(&in_rvous[i],&tmptris[i],sizeof(Tri));
  }

  // insure mytris is allocated sufficient for new tris
  // reset nown to new value after rendezvous

  if (nnew > maxown) {
    int old = maxown;
    maxown = nnew;
    grow_own(old);
  }
  nown = nnew;

  // perform rendezvous operation
  // each proc owns subset of new surfs
  // receives them from other procs

  char *buf;
  int nout = comm->rendezvous(1,nsend,(char *) in_rvous,sizeof(Tri),
                              0,proclist,rendezvous_tris,
                              0,buf,0,(void *) this);

  memory->destroy(proclist);
  memory->sfree(in_rvous);
}

/* ----------------------------------------------------------------------
   callback from rendezvous operation
   store received surfs assigned to me in correct location in mytris
   inbuf = list of N Inbuf datums
   no outbuf
------------------------------------------------------------------------- */

int Surf::rendezvous_tris(int n, char *inbuf,
                          int &flag, int *&proclist, char *&outbuf,
                          void *ptr)
{
  int i,j,k,m;

  Surf *sptr = (Surf *) ptr;
  Tri *tris = sptr->mytris;
  int nprocs = sptr->comm->nprocs;
  int me = sptr->comm->me;

  // zero my owned surf values

  Tri *in_rvous = (Tri *) inbuf;
  surfint id;

  for (int i = 0; i < n; i++) {
    id = in_rvous[i].id;
    m = (id-1-me) / nprocs;
    memcpy(&tris[m],&in_rvous[i],sizeof(Tri));
  }

  // flag = 0: no second comm needed in rendezvous

  flag = 0;
  return 0;
}

// ----------------------------------------------------------------------
// methods for per-surf custom attributes
// ----------------------------------------------------------------------

/* ----------------------------------------------------------------------
   find custom per-atom vector/array with name
   return index if found
   return -1 if not found
------------------------------------------------------------------------- */

int Surf::find_custom(char *name)
{
  for (int i = 0; i < ncustom; i++)
    if (ename[i] && strcmp(ename[i],name) == 0) return i;
  return -1;
}

/* ----------------------------------------------------------------------
   add a custom attribute with name
   assumes name does not already exist, except in case of restart
   type = 0/1 for int/double
   size = 0 for vector, size > 0 for array with size columns
   return index of its location
------------------------------------------------------------------------- */

int Surf::add_custom(char *name, int type, int size)
{
  int index;

  // if name already exists
  // just return index if a restart script and re-defining the name
  // else error

  index = find_custom(name);
  if (index >= 0) {
    if (custom_restart_flag == NULL || custom_restart_flag[index] == 1)
      error->all(FLERR,"Custom surf attribute name already exists");
    custom_restart_flag[index] = 1;
    return index;
  }

  // use first available NULL entry or allocate a new one

  for (index = 0; index < ncustom; index++)
    if (ename[index] == NULL) break;

  if (index == ncustom) {
    ncustom++;
    ename = (char **) memory->srealloc(ename,ncustom*sizeof(char *),
                                       "surf:ename");
    memory->grow(etype,ncustom,"surf:etype");
    memory->grow(esize,ncustom,"surf:etype");
    memory->grow(ewhich,ncustom,"surf:etype");
  }

  int n = strlen(name) + 1;
  ename[index] = new char[n];
  strcpy(ename[index],name);
  etype[index] = type;
  esize[index] = size;

  if (type == INT) {
    if (size == 0) {
      ewhich[index] = ncustom_ivec++;
      eivec = (int **)
        memory->srealloc(eivec,ncustom_ivec*sizeof(int *),"surf:eivec");
      memory->grow(icustom_ivec,ncustom_ivec,"surf:icustom_ivec");
      icustom_ivec[ncustom_ivec-1] = index;
    } else {
      ewhich[index] = ncustom_iarray++;
      eiarray = (int ***)
        memory->srealloc(eiarray,ncustom_iarray*sizeof(int **),
                         "surf:eiarray");
      memory->grow(icustom_iarray,ncustom_iarray,"surf:icustom_iarray");
      icustom_iarray[ncustom_iarray-1] = index;
      memory->grow(eicol,ncustom_iarray,"surf:eicol");
      eicol[ncustom_iarray-1] = size;
    }
  } else if (type == DOUBLE) {
    if (size == 0) {
      ewhich[index] = ncustom_dvec++;
      edvec = (double **)
        memory->srealloc(edvec,ncustom_dvec*sizeof(double *),"surf:edvec");
      memory->grow(icustom_dvec,ncustom_dvec,"surf:icustom_dvec");
      icustom_dvec[ncustom_dvec-1] = index;
    } else {
      ewhich[index] = ncustom_darray++;
      edarray = (double ***)
        memory->srealloc(edarray,ncustom_darray*sizeof(double **),
                         "surf:edarray");
      memory->grow(icustom_darray,ncustom_darray,"surf:icustom_darray");
      icustom_darray[ncustom_darray-1] = index;
      memory->grow(edcol,ncustom_darray,"surf:edcol");
      edcol[ncustom_darray-1] = size;
    }
  }

  allocate_custom(index,nlocal);

  return index;
}

/* ----------------------------------------------------------------------
   allocate vector/array associated with custom attribute with index
   set new values to 0 via memset()
------------------------------------------------------------------------- */

void Surf::allocate_custom(int index, int n)
{
  if (etype[index] == INT) {
    if (esize[index] == 0) {
      int *ivector = memory->create(eivec[ewhich[index]],n,"surf:eivec");
      if (ivector) memset(ivector,0,n*sizeof(int));
    } else {
      int **iarray = memory->create(eiarray[ewhich[index]],
                                    n,eicol[ewhich[index]],"surf:eiarray");
      if (iarray) memset(&iarray[0][0],0,n*eicol[ewhich[index]]*sizeof(int));
    }

  } else {
    if (esize[index] == 0) {
      double *dvector = memory->create(edvec[ewhich[index]],n,"surf:edvec");
      if (dvector) memset(dvector,0,n*sizeof(double));
    } else {
      double **darray = memory->create(edarray[ewhich[index]],
                                       n,edcol[ewhich[index]],"surf:eearray");
      if (darray) memset(&darray[0][0],0,n*edcol[ewhich[index]]*sizeof(double));
    }
  }
}

/* ----------------------------------------------------------------------
   remove a custom attribute at location index
   free memory for name and vector/array and set ptrs to NULL
   ncustom lists never shrink, but indices stored between
     the ncustom list and the dense vector/array lists must be reset
------------------------------------------------------------------------- */

void Surf::remove_custom(int index)
{
  delete [] ename[index];
  ename[index] = NULL;

  if (etype[index] == INT) {
    if (esize[index] == 0) {
      memory->destroy(eivec[ewhich[index]]);
      ncustom_ivec--;
      for (int i = ewhich[index]; i < ncustom_ivec; i++) {
        icustom_ivec[i] = icustom_ivec[i+1];
        ewhich[icustom_ivec[i]] = i;
        eivec[i] = eivec[i+1];
      }
    } else{
      memory->destroy(eiarray[ewhich[index]]);
      ncustom_iarray--;
      for (int i = ewhich[index]; i < ncustom_iarray; i++) {
        icustom_iarray[i] = icustom_iarray[i+1];
        ewhich[icustom_iarray[i]] = i;
        eiarray[i] = eiarray[i+1];
        eicol[i] = eicol[i+1];
      }
    }
  } else if (etype[index] == DOUBLE) {
    if (esize[index] == 0) {
      memory->destroy(edvec[ewhich[index]]);
      ncustom_dvec--;
      for (int i = ewhich[index]; i < ncustom_dvec; i++) {
        icustom_dvec[i] = icustom_dvec[i+1];
        ewhich[icustom_dvec[i]] = i;
        edvec[i] = edvec[i+1];
      }
    } else{
      memory->destroy(edarray[ewhich[index]]);
      ncustom_darray--;
      for (int i = ewhich[index]; i < ncustom_darray; i++) {
        icustom_darray[i] = icustom_darray[i+1];
        ewhich[icustom_darray[i]] = i;
        edarray[i] = edarray[i+1];
        edcol[i] = edcol[i+1];
      }
    }
  }

  // set ncustom = 0 if custom list is now entirely empty

  int empty = 1;
  for (int i = 0; i < ncustom; i++)
    if (ename[i]) empty = 0;
  if (empty) ncustom = 0;
}

// ----------------------------------------------------------------------
// methods for write/read restart info
// ----------------------------------------------------------------------

/* ----------------------------------------------------------------------
   proc 0 writes surf geometry to restart file
   NOTE: needs to be generalized for distributed or implicit surfs
------------------------------------------------------------------------- */

void Surf::write_restart(FILE *fp)
{
  if (distributed || implicit)
    error->all(FLERR,
               "Restart files with distributed surfaces are not yet supported");

  fwrite(&ngroup,sizeof(int),1,fp);

  int n;
  for (int i = 0; i < ngroup; i++) {
    n = strlen(gnames[i]) + 1;
    fwrite(&n,sizeof(int),1,fp);
    fwrite(gnames[i],sizeof(char),n,fp);
  }

  if (domain->dimension == 2) {
    fwrite(&nsurf,sizeof(bigint),1,fp);
    for (int i = 0; i < nsurf; i++) {
      fwrite(&lines[i].id,sizeof(surfint),1,fp);
      fwrite(&lines[i].type,sizeof(int),1,fp);
      fwrite(&lines[i].mask,sizeof(int),1,fp);
      fwrite(&lines[i].transparent,sizeof(int),1,fp);
      fwrite(lines[i].p1,sizeof(double),3,fp);
      fwrite(lines[i].p2,sizeof(double),3,fp);
    }
  }

  if (domain->dimension == 3) {
    fwrite(&nsurf,sizeof(bigint),1,fp);
    for (int i = 0; i < nsurf; i++) {
      fwrite(&tris[i].id,sizeof(surfint),1,fp);
      fwrite(&tris[i].type,sizeof(int),1,fp);
      fwrite(&tris[i].mask,sizeof(int),1,fp);
      fwrite(&tris[i].transparent,sizeof(int),1,fp);
      fwrite(tris[i].p1,sizeof(double),3,fp);
      fwrite(tris[i].p2,sizeof(double),3,fp);
      fwrite(tris[i].p3,sizeof(double),3,fp);
    }
  }
}

/* ----------------------------------------------------------------------
   proc 0 reads surf geometry from restart file
   bcast to other procs
   NOTE: needs to be generalized for distributed or implicit surfs
------------------------------------------------------------------------- */

void Surf::read_restart(FILE *fp)
{
  int tmp;

  if (distributed || implicit)
    error->all(FLERR,
               "Restart files with distributed surfaces are not yet supported");

  int me = comm->me;

  // if any exist, clear existing group names, before reading new ones

  for (int i = 0; i < ngroup; i++) delete [] gnames[i];

  if (me == 0) tmp = fread(&ngroup,sizeof(int),1,fp);
  MPI_Bcast(&ngroup,1,MPI_INT,0,world);

  int n;
  for (int i = 0; i < ngroup; i++) {
    if (me == 0) tmp = fread(&n,sizeof(int),1,fp);
    MPI_Bcast(&n,1,MPI_INT,0,world);
    gnames[i] = new char[n];
    if (me == 0) tmp = fread(gnames[i],sizeof(char),n,fp);
    MPI_Bcast(gnames[i],n,MPI_CHAR,0,world);
  }

  if (domain->dimension == 2) {
    if (me == 0) tmp = fread(&nsurf,sizeof(bigint),1,fp);
    MPI_Bcast(&nsurf,1,MPI_SPARTA_BIGINT,0,world);
    lines = (Line *) memory->smalloc(nsurf*sizeof(Line),"surf:lines");
    // NOTE: need different logic for different surf styles
    nlocal = nsurf;
    nmax = nlocal;

    if (me == 0) {
      for (int i = 0; i < nsurf; i++) {
        tmp = fread(&lines[i].id,sizeof(surfint),1,fp);
        tmp = fread(&lines[i].type,sizeof(int),1,fp);
        tmp = fread(&lines[i].mask,sizeof(int),1,fp);
        tmp = fread(&lines[i].transparent,sizeof(int),1,fp);
        lines[i].isc = lines[i].isr = -1;
        tmp = fread(lines[i].p1,sizeof(double),3,fp);
        tmp = fread(lines[i].p2,sizeof(double),3,fp);
        lines[i].norm[0] = lines[i].norm[1] = lines[i].norm[2] = 0.0;
      }
    }
    if (nsurf*sizeof(Line) > MAXSMALLINT)
      error->all(FLERR,"Surf restart memory exceeded");
    MPI_Bcast(lines,nsurf*sizeof(Line),MPI_CHAR,0,world);
  }

  if (domain->dimension == 3) {
    if (me == 0) tmp = fread(&nsurf,sizeof(bigint),1,fp);
    MPI_Bcast(&nsurf,1,MPI_SPARTA_BIGINT,0,world);
    tris = (Tri *) memory->smalloc(nsurf*sizeof(Tri),"surf:tris");
    // NOTE: need different logic for different surf styles
    nlocal = nsurf;
    nmax = nlocal;

    if (me == 0) {
      for (int i = 0; i < nsurf; i++) {
        tmp = fread(&tris[i].id,sizeof(surfint),1,fp);
        tmp = fread(&tris[i].type,sizeof(int),1,fp);
        tmp = fread(&tris[i].mask,sizeof(int),1,fp);
        tmp = fread(&tris[i].transparent,sizeof(int),1,fp);
        tris[i].isc = tris[i].isr = -1;
        tmp = fread(tris[i].p1,sizeof(double),3,fp);
        tmp = fread(tris[i].p2,sizeof(double),3,fp);
        tmp = fread(tris[i].p3,sizeof(double),3,fp);
        tris[i].norm[0] = tris[i].norm[1] = tris[i].norm[2] = 0.0;
      }
    }
    if (nsurf*sizeof(Tri) > MAXSMALLINT)
      error->all(FLERR,"Surf restart memory exceeded");
    MPI_Bcast(tris,nsurf*sizeof(Tri),MPI_CHAR,0,world);
  }
}

/* ----------------------------------------------------------------------
   proc 0 writes custom attribute definition info to restart file
------------------------------------------------------------------------- */

void Surf::write_restart_custom(FILE *fp)
{
  int m,index;

  // nactive = # of ncustom that have active vectors/arrays

  int nactive = 0;
  for (int i = 0; i < ncustom; i++)
    if (ename[i]) nactive++;

  fwrite(&nactive,sizeof(int),1,fp);

  // must write custom info in same order
  //   the per-surf custom values will be written into file
  // not necessarily the same as ncustom list, due to deletions & additions

  for (m = 0; m < ncustom_ivec; m++) {
    index = icustom_ivec[m];
    int n = strlen(ename[index]) + 1;
    fwrite(&n,sizeof(int),1,fp);
    fwrite(ename[index],sizeof(char),n,fp);
    fwrite(&etype[index],sizeof(int),1,fp);
    fwrite(&esize[index],sizeof(int),1,fp);
  }
  for (m = 0; m < ncustom_iarray; m++) {
    index = icustom_iarray[m];
    int n = strlen(ename[index]) + 1;
    fwrite(&n,sizeof(int),1,fp);
    fwrite(ename[index],sizeof(char),n,fp);
    fwrite(&etype[index],sizeof(int),1,fp);
    fwrite(&esize[index],sizeof(int),1,fp);
  }
  for (m = 0; m < ncustom_dvec; m++) {
    index = icustom_dvec[m];
    int n = strlen(ename[index]) + 1;
    fwrite(&n,sizeof(int),1,fp);
    fwrite(ename[index],sizeof(char),n,fp);
    fwrite(&etype[index],sizeof(int),1,fp);
    fwrite(&esize[index],sizeof(int),1,fp);
  }
  for (m = 0; m < ncustom_darray; m++) {
    index = icustom_darray[m];
    int n = strlen(ename[index]) + 1;
    fwrite(&n,sizeof(int),1,fp);
    fwrite(ename[index],sizeof(char),n,fp);
    fwrite(&etype[index],sizeof(int),1,fp);
    fwrite(&esize[index],sizeof(int),1,fp);
  }
}

/* ----------------------------------------------------------------------
   proc 0 reads custom attribute definition info from restart file
   bcast to other procs and all procs instantiate series of custom properties
------------------------------------------------------------------------- */

void Surf::read_restart_custom(FILE *fp)
{
  int tmp;

  // ncustom is 0 at time restart file is read
  // will be incremented as add_custom() for each nactive

  int nactive;
  if (me == 0) tmp = fread(&nactive,sizeof(int),1,fp);
  MPI_Bcast(&nactive,1,MPI_INT,0,world);
  if (nactive == 0) return;

  // order that custom vectors/arrays are in restart file
  //   matches order the per-particle custom values will be read from file

  int n,type,size,ghostflag;
  char *name;

  for (int i = 0; i < nactive; i++) {
    if (me == 0) tmp = fread(&n,sizeof(int),1,fp);
    MPI_Bcast(&n,1,MPI_INT,0,world);
    name = new char[n];
    if (me == 0) tmp = fread(name,sizeof(char),n,fp);
    MPI_Bcast(name,n,MPI_CHAR,0,world);
    if (me == 0) tmp = fread(&type,sizeof(int),1,fp);
    MPI_Bcast(&type,n,MPI_CHAR,0,world);
    if (me == 0) tmp = fread(&size,sizeof(int),1,fp);
    MPI_Bcast(&size,n,MPI_CHAR,0,world);

    // create the custom attribute

    add_custom(name,type,size);
    delete [] name;
  }

  // set flag for each newly created custom attribute to 0
  // will be reset to 1 if restart script redefines attribute with same name

  custom_restart_flag = new int[ncustom];
  for (int i = 0; i < ncustom; i++) custom_restart_flag[i] = 0;
}

// ----------------------------------------------------------------------
// methods for growing line/tri data structs
// ----------------------------------------------------------------------

/* ---------------------------------------------------------------------- */

void Surf::grow(int old)
{
  if (nmax <= old) return;

  if (domain->dimension == 2) {
    lines = (Surf::Line *)
      memory->srealloc(lines,nmax*sizeof(Line),"surf:lines");
    memset(&lines[old],0,(nmax-old)*sizeof(Line));
  } else {
    tris = (Surf::Tri *)
      memory->srealloc(tris,nmax*sizeof(Tri),"surf:tris");
    memset(&tris[old],0,(nmax-old)*sizeof(Tri));
  }
}

/* ---------------------------------------------------------------------- */

void Surf::grow_own(int old)
{
  if (domain->dimension == 2) {
    mylines = (Surf::Line *)
      memory->srealloc(mylines,maxown*sizeof(Line),"surf:mylines");
    memset(&mylines[old],0,(maxown-old)*sizeof(Line));
  } else {
    mytris = (Surf::Tri *)
      memory->srealloc(mytris,maxown*sizeof(Tri),"surf:mytris");
    memset(&mytris[old],0,(maxown-old)*sizeof(Tri));
  }
}

/* ---------------------------------------------------------------------- */

void Surf::grow_temporary(int old)
{
  if (domain->dimension == 2) {
    tmplines = (Surf::Line *)
      memory->srealloc(tmplines,nmaxtmp*sizeof(Line),"surf:lines");
    memset(&tmplines[old],0,(nmaxtmp-old)*sizeof(Line));
  } else {
    tmptris = (Surf::Tri *)
      memory->srealloc(tmptris,nmaxtmp*sizeof(Tri),"surf:tris");
    memset(&tmptris[old],0,(nmaxtmp-old)*sizeof(Tri));
  }
}

/* ---------------------------------------------------------------------- */

bigint Surf::memory_usage()
{
  bigint bytes = 0;

  if (implicit) {
    if (domain->dimension == 2) bytes += nlocal * sizeof(Line);
    else bytes += nlocal * sizeof(Tri);
  } else if (distributed) {
    if (domain->dimension == 2) bytes += (nlocal+nghost) * sizeof(Line);
    else bytes += (nlocal+nghost) * sizeof(Tri);
    if (domain->dimension == 2) bytes += nown * sizeof(Line);
    else bytes += nown * sizeof(Tri);
  } else {
    if (domain->dimension == 2) bytes += nsurf * sizeof(Line);
    else bytes += nsurf * sizeof(Tri);
    bytes += nlocal * sizeof(int);
  }

  return bytes;
}

/* ----------------------------------------------------------------------
	 Determines corner values given an explicit surface. Cvalues then used
	 later in ablate to create the implicit surfaces
------------------------------------------------------------------------- */

void Surf::set_corners()
{
  Grid::ChildCell *cells = grid->cells;
  Grid::ChildInfo *cinfo = grid->cinfo;
	double xo[3]; // outside point
	double cx[8], cy[8], cz[8]; // store all corners
	double p1[3], p2[3]; // corner coordinate
  double pp[3], pm[3];
	int ioc; // flag if point is outside of inside surface
  int itype; // inside or outside cell?
  int ix, iy, iz;
	double xc,yc,zc;
	double xl[2], yl[2], zl[2];

  int hitflag, isurf, nsurf;

  double lo[3], hi[3];
  lo[0] = domain->boxhi[0];
  lo[1] = domain->boxhi[1];
  lo[2] = domain->boxhi[2];
  hi[0] = domain->boxlo[0];
  hi[1] = domain->boxlo[1];
  hi[2] = domain->boxlo[2];

  int ic[3], xyzcell;
  double lc[3];

  // first shift everything down by thresh
  // later shift back
  cout = 0.0;
  cin = 255.0;

  // initialize cvalues as all out
  for (int i = 0; i < Nxyz; i++) cvalues[i] = -1.0;

  // find corner values
  if(domain->dimension==2) {
    set_surfcell2d();
  } else {
    set_surfcell3d();
  }

	// store into icvalues for generating implicit surface
	for(int icell = 0; icell < grid->nlocal; icell++) {

    lc[0] = cells[icell].lo[0];
    lc[1] = cells[icell].lo[1];
    lc[2] = cells[icell].lo[2];

    xyzcell = get_cxyz(ic,lc);
    icvalues[icell][0] = cvalues[xyzcell];
    xyzcell = get_corner(ic[0]+1, ic[1], ic[2]);
    icvalues[icell][1] = cvalues[xyzcell];
    xyzcell = get_corner(ic[0], ic[1]+1, ic[2]);
    icvalues[icell][2] = cvalues[xyzcell];
    xyzcell = get_corner(ic[0]+1, ic[1]+1, ic[2]);
    icvalues[icell][3] = cvalues[xyzcell];


    if(domain->dimension==3) {
      xyzcell = get_corner(ic[0], ic[1], ic[2]+1);
      icvalues[icell][4] = cvalues[xyzcell];
      xyzcell = get_corner(ic[0]+1, ic[1], ic[2]+1);
      icvalues[icell][5] = cvalues[xyzcell];
      xyzcell = get_corner(ic[0], ic[1]+1, ic[2]+1);
      icvalues[icell][6] = cvalues[xyzcell];
      xyzcell = get_corner(ic[0]+1, ic[1]+1, ic[2]+1);
      icvalues[icell][7] = cvalues[xyzcell];
    }
  }

  //error->one(FLERR,"check");
	return;
}

/* ----------------------------------------------------------------------
   Same as above but outside points in unknown cells (cells with surfaces)
   are set as the thrshold. The inner points in unknown cells are set
   as the averge of the cvalues needed to get an exact representation
------------------------------------------------------------------------- */

void Surf::set_surfcell2d()
{
  Grid::ChildCell *cells = grid->cells;
  Grid::ChildInfo *cinfo = grid->cinfo;
	double cx[8], cy[8], cz[8]; // store all corners
	double pi[3], pj[3]; // corner coordinate
  int itype; // inside or outside cell?

  int hitflag, isurf, nsurf;
  Surf::Line *line;
  Surf::Line *lines = surf->lines;
  surfint *csurfs;

  // number of points around corner point
  int npairs = 4;
  // mvalues stores minimum param
  // also used to determine side
  memory->create(mvalues,Nxyz,"surf:mvalues");
  // svalues stores side of minimum param
  memory->create(svalues,Nxyz,"surf:svalues");
  // array to keep track of param between corners
  // each corner has 4 neighbors
  // -x, +x, -y, +y
  // only recrod neighbor to right and top
  memory->create(ivalues,Nxyz,npairs,"surf:ivalues");
	
  for(int ic = 0; ic < Nxyz; ic++) {
    svalues[ic] = -1;
    mvalues[ic] = -1.0;
    for(int jc = 0; jc < npairs; jc++) ivalues[ic][jc] = -1.0;
  }

  double param; // point of intersection as fraction along p1->p2
  int side; // hit inside or outside
  int onsurf; // handles surfaces very close to cell boundary

  // number of edges in a cell
  int nedge = 4;
  int ci[4], cj[4];
  ci[0] = 0; cj[0] = 1;
  ci[1] = 1; cj[1] = 3;
  ci[2] = 3; cj[2] = 2;
  ci[3] = 2; cj[3] = 0;

  // first determine the intersection values/count for each corner
  int xyzcell, xyzp1, xyzp2;
  int n1, n2;
	for(int icell = 0; icell < grid->nlocal; icell++) {

    // if no surfs, continue
    nsurf = cells[icell].nsurf;
    if(!nsurf) continue;

    for(int d = 0; d < 3; d++) {
      cl[d] = cells[icell].lo[d];
      ch[d] = cells[icell].hi[d];
    }

		// store cell corners
    cx[0] = cx[2] = cl[0];
    cx[1] = cx[3] = ch[0];

    cy[0] = cy[1] = cl[1];
    cy[2] = cy[3] = ch[1];

    // zero out z-direction
    cz[0] = cz[1] = cz[2] = cz[3] = 0.0;

    // smallest cell length
    // should only have to do this once
    mind = std::min(ch[0]-cl[0], ch[1]-cl[1]);

		// determine corner values
    csurfs = cells[icell].csurfs;
		for(int ic = 0; ic < nedge; ic++) {
      int i = ci[ic];
      pi[0] = cx[i];
      pi[1] = cy[i];
      pi[2] = cz[i];

      int j = cj[ic];
      pj[0] = cx[j];
      pj[1] = cy[j];
      pj[2] = cz[j];

      // get index for p1 and p2
      // c1 is always lower from above
      int c1 = get_corner(pi[0], pi[1], pi[2]);
      int c2 = get_corner(pj[0], pj[1], pj[2]);

      // test all surfs+corners to see if any hit
      for (int m = 0; m < nsurf; m++) {
        isurf = csurfs[m];
        line = &lines[isurf];

        // always start with lower corner
        // side will always be either 0 or 1
        hitflag = corner_hit2d(pi, pj, line, param, side, onsurf);

        // need to take care of values near machine precision
        if(param < EPSSURF*mind) param = 0.0;
        if((1.0-param) < EPSSURF*mind) param = 1.0;

        // once a hit is found
        if(hitflag) {

          if(ic==0) {
            n1 = 1;
            n2 = 0;
          } else if(ic==1) {
            n1 = 3;
            n2 = 2;
          } else if(ic==2) {
            n1 = 0;
            n2 = 1;
          } else {
            n1 = 2;
            n2 = 3;
          }

          if(ivalues[c1][n1] > param || ivalues[c1][n1] < 0) ivalues[c1][n1] = param;
          if(ivalues[c2][n2] > (1.0-param) || ivalues[c2][n2] < 0) ivalues[c2][n2] = 1.0-param;

          if(mvalues[c1] < 0 || param <= mvalues[c1]) {
            if(param == 0) svalues[c1] = 0;
            else if(svalues[c1] == 2) 0; // do nothing
            // conflicting sides from two surfaces meeting at corner
            else if(std::abs(mvalues[c1]-param) < EPSSURF && svalues[c1] != side) svalues[c1] = 2;
            else svalues[c1] = side;

            mvalues[c1] = param;
          }

          if(mvalues[c2] < 0 || (1.0-param) <= mvalues[c2]) {
            if((1.0-param) == 0) svalues[c2] = 0;
            else if(svalues[c2] == 2) 0; // do nothing
            else if(std::abs(mvalues[c2]-(1.0-param)) < EPSSURF && svalues[c2] != !side) svalues[c2] = 2;
            else svalues[c2] = !side;

            mvalues[c2] = 1.0-param;
          }

        } // end "if" hitflag
      }// end "for" for surfaces
		}// end "for" for corners in cellfe
    //if(icell > 50) error->one(FLERR,"check");
	}// end "for" for grid cells

  // now set in/out dependent on cell type
  int sval;
  int cxyz[3];
	for(int icell = 0; icell < grid->nlocal; icell++) {

    cl[0] = cells[icell].lo[0];
    cl[1] = cells[icell].lo[1];
    cl[2] = cells[icell].lo[2];
    xyzcell = get_cxyz(cxyz,cl);

    // itype = 1 - fully outside
    // itype = 2 - fully inside
    // itype = 3 - has surfaces
    // cannot just use types, if surface on corner
    // .. can be either 2 or 3 depending on which corner (ambiguity)
    itype = cinfo[icell].type;

    // fully inside so set all corner values to max
    if(itype==2) {
      sval = 1;
    // fully outside so set all corners to min
    } else if (itype==1) {
      sval = 0;
    } else {
      continue;
    }

    // set corners if not already set
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;
    xyzcell = get_corner(cxyz[0]+1, cxyz[1], cxyz[2]);
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;
    xyzcell = get_corner(cxyz[0], cxyz[1]+1, cxyz[2]);
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;
    xyzcell = get_corner(cxyz[0]+1, cxyz[1]+1, cxyz[2]);
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;
  }

  // lastly handle ambiguous cases based on neighbors
  // .. which do not intersect with a surface (intersect)
  int j; // test neighbor
  for(int i = 0; i < Nxyz; i++) {
    if(svalues[i] == 0 || svalues[i] == 1) continue;
    //printf("i: %i\n", i);

    // try x-neighbor
    j = i - 1;
    if(j >= 0 && ivalues[i][0] < 0) {
      svalues[i] = svalues[j];
      continue;
    }

    j = i + 1;
    if(j < Nxyz && ivalues[i][1] < 0) {
      svalues[i] = svalues[j];
      continue;
    }

    // try y-neighbor
    j = i - (nxyz[0]+1);
    if(j >= 0 && ivalues[i][2] < 0) {
      svalues[i] = svalues[j];
      continue;
    }

    j = i + (nxyz[0]+1);
    if(j < Nxyz && ivalues[i][3] < 0) {
      svalues[i] = svalues[j];
      continue;
    }

    error->one(FLERR,"cannot find reference");
  }

  // initially set inside as cin and outside as cout
  if(aveFlag) {
    int nval;
    double ivalsum;
	  for(int i = 0; i < Nxyz; i++) {
      ivalsum = 0.0;
      if(svalues[i] == 0) cvalues[i] = cout;
      else {
        nval = 0;
        for(int j = 0; j < npairs; j++) {
          if(ivalues[i][j] >= 0) {
            ivalsum += ivalues[i][j];
            nval++;
          }
        }

        // no intersections
        if(nval == 0) cvalues[i] = cin;
        // need to set these points as outside to avoid very small volume error
        else if(ivalsum == 0) cvalues[i] = MAX(thresh-1,cout);
        else {
          cvalues[i] = param2in(ivalsum/nval,0.0);
        }
      }
	  }// end "for" for grid cells

  // find cvalues by solving linear systems
  } else {
    for(int i = 0; i < Nxyz; i++) {
      if(svalues[i] == 0) cvalues[i] = cout;
      else if(svalues[i] == 1) cvalues[i] = cin;
    }// end "for" for grid cells
  }

  // free up memory
  memory->destroy(ivalues);
  memory->destroy(mvalues);
  memory->destroy(svalues);

  //error->one(FLERR,"check");
	return;
}

/* ----------------------------------------------------------------------
	 Determines if surface is inline with cell edge. Onsurf input should be 
   false. Onsurf can only be set to true or unchanged

   Side = 0,1,2 -> [out,in,onsurf]
------------------------------------------------------------------------- */

int Surf::corner_hit2d(double *p1, double *p2,
    Line *line, double &param, int &side, int& onsurf)
{
  onsurf = 0;

  // try intersect first
  int h, tside;
  double tparam;
  double d3dum[3];
  h = Geometry::
    line_line_intersect(p1,p2,line->p1,line->p2,line->norm,d3dum,tparam,tside);
  if(h) {
    if(tparam < EPSSURF || (1.0-tparam) < EPSSURF) onsurf = 1;
    if(tside == 1 || tside == 2 || tside == 5) {
      side = 1;
      param = tparam;
      return true;
    } else {
      side = 0;
      param = tparam;
      return true;
    }
  }

  onsurf = 1;
  // perturbed points
  double p1p[3];
  double p2p[3];

  double dx[8], dy[8];
  double dp = mind/1000.0;
  dx[0] = dx[1] = dx[6] = dp;
  dx[2] = dx[5] = 0;
  dx[3] = dx[4] = dx[7] = -dp;

  dy[0] = dy[2] = dy[7] = dp;
  dy[1] = dy[4] = 0;
  dy[3] = dy[5] = dy[6] = -dp;

  for(int i = 0; i < 8; i++) {
    p1p[2] = p1[2];
    p2p[2] = p2[2];

    p1p[0] = p1[0] + dx[i];
    p1p[1] = p1[1] + dy[i];

    p2p[0] = p2[0] + dx[i];
    p2p[1] = p2[1] + dy[i];

    h = Geometry::
      line_line_intersect(p1p,p2p,line->p1,line->p2,line->norm,d3dum,tparam,tside);
    if(h) {
      if(tside == 1 || tside == 2 || tside == 5) {
        //side = 2;
        side = 1;
        if(tparam<0.5) param = 0.0;
        else param = 1.0;
        return true;
      } else {
        //side = 2;
        side = 0;
        if(tparam<0.5) param = 0.0;
        else param = 1.0;
        return true;
      }
    }
  }

  // true miss
  return false;
}

/* ----------------------------------------------------------------------
	 Find inside corner value from corner value
------------------------------------------------------------------------- */
double Surf::param2in(double param, double v1)
{
  double v0;
  // param is proportional to cell length so 
  // ... lo = 0; hi = 1
  // trying to find v0
  // param = (thresh  - v0) / (v1 - v0)
  if(param == 1.0) return 255.0;
  v0 = (thresh - v1*param) / (1.0 - param);

  // bound by limits
  //v0 = MAX(v0,thresh);
  v0 = MIN(v0,255.0);
  return v0;
}

/* ----------------------------------------------------------------------
	 Find outside corner value from corner value
------------------------------------------------------------------------- */
double Surf::param2out(double param, double v0)
{
  double v1;
  // param is proportional to cell length so 
  // ... lo = 0; hi = 1
  // trying to find v0
  // param = (thresh  - v0) / (v1 - v0)
  if(param == 0.0) return 255.0;
  v1 = ((thresh - v0) / param) + v0;

  // bound by limits
  //v1 = MAX(v1,thresh);
  v1 = MIN(v1,255.0);
  return v1;
}

/* ----------------------------------------------------------------------
   Same as set_surfcell2d but for 3d
------------------------------------------------------------------------- */

void Surf::set_surfcell3d()
{
  Grid::ChildCell *cells = grid->cells;
  Grid::ChildInfo *cinfo = grid->cinfo;
	double cx[8], cy[8], cz[8]; // store all corners
	double pi[3], pj[3]; // corner coordinate
  int itype; // inside or outside cell?

  int hitflag, isurf, nsurf;
  Surf::Tri *tri;
  Surf::Tri *tris = surf->tris;
  surfint *csurfs;

  // number of points around corner point
  int npairs = 6;
  // mvalues stores minimum param
  // also used to determine side
  memory->create(mvalues,Nxyz,"surf:mvalues");
  // svalues stores side of minimum param
  memory->create(svalues,Nxyz,"surf:svalues");
  // array to keep track of param between corners
  // each corner has 4 neighbors
  // -x, +x, -y, +y
  // only recrod neighbor to right and top
  memory->create(ivalues,Nxyz,npairs,"surf:ivalues");

  for(int ic = 0; ic < Nxyz; ic++) {
    svalues[ic] = -1;
    mvalues[ic] = -1.0;
    for(int jc = 0; jc < npairs; jc++) ivalues[ic][jc] = -1.0;
  }

  double param; // point of intersection as fraction along p1->p2
  int side; // hit inside or outside
  int onsurf; // handles surfaces very close to cell boundary

  // number of edges in a cell
  int nedge = 12;
  int ci[12], cj[12];
  ci[0] = 0; cj[0] = 1;
  ci[1] = 1; cj[1] = 3;
  ci[2] = 3; cj[2] = 2;
  ci[3] = 2; cj[3] = 0;
  ci[4] = 0; cj[4] = 4;
  ci[5] = 1; cj[5] = 5;
  ci[6] = 3; cj[6] = 7;
  ci[7] = 2; cj[7] = 6;
  ci[8] = 4; cj[8] = 5;
  ci[9] = 5; cj[9] = 7;
  ci[10] = 7; cj[10] = 6;
  ci[11] = 6; cj[11] = 4;

  // first determine the intersection values/count for each corner
  int xyzcell;
  int n1, n2;
	for(int icell = 0; icell < grid->nlocal; icell++) {

    // if no surfs, continue
    nsurf = cells[icell].nsurf;
    if(!nsurf) continue;

    for(int d = 0; d < 3; d++) {
      cl[d] = cells[icell].lo[d];
      ch[d] = cells[icell].hi[d];
    }

    cx[0] = cx[2] = cx[4] = cx[6] = cl[0];
    cx[1] = cx[3] = cx[5] = cx[7] = ch[0];

    cy[0] = cy[1] = cy[4] = cy[5] = cl[1];
    cy[2] = cy[3] = cy[6] = cy[7] = ch[1];

    cz[0] = cz[1] = cz[2] = cz[3] = cl[2];
    cz[4] = cz[5] = cz[6] = cz[7] = ch[2];

    // smallest cell length
    // should only have to do this once
    mind = std::min(ch[0]-cl[0], ch[1]-cl[1]);
    mind = std::min(mind, ch[2]-cl[2]);

		// determine corner values
    csurfs = cells[icell].csurfs;
		for(int ic = 0; ic < nedge; ic++) {
      int i = ci[ic];
      pi[0] = cx[i];
      pi[1] = cy[i];
      pi[2] = cz[i];

      int j = cj[ic];
      pj[0] = cx[j];
      pj[1] = cy[j];
      pj[2] = cz[j];

      // get corners
      int c1 = get_corner(pi[0], pi[1], pi[2]);
      int c2 = get_corner(pj[0], pj[1], pj[2]);

      // test all surfs+corners to see if any hit
      for (int m = 0; m < nsurf; m++) {
        isurf = csurfs[m];
        tri = &tris[isurf];
        hitflag = corner_hit3d(pi, pj, tri, param, side, onsurf);

        // need to take care of values near machine precision
        if(param < EPSSURF*mind) param = 0.0;
        if((1.0-param) < EPSSURF*mind) param = 1.0;

        // once a hit is found
        if(hitflag) {

          if(ic==0 || ic==8) {
            n1 = 1;
            n2 = 0;
          } else if(ic==1 || ic==9) {
            n1 = 3;
            n2 = 2;
          } else if(ic==2 || ic==10) {
            n1 = 0;
            n2 = 1;
          } else if(ic==3 || ic==11) {
            n1 = 2;
            n2 = 3;
          } else {
            n1 = 5;
            n2 = 4;
          }

          if(ivalues[c1][n1] > param || ivalues[c1][n1] < 0) ivalues[c1][n1] = param;
          if(ivalues[c2][n2] > (1.0-param) || ivalues[c2][n2] < 0) ivalues[c2][n2] = 1.0-param;

          if(mvalues[c1] < 0 || param <= mvalues[c1]) {
            if(param == 0) svalues[c1] = 0;
            else if(svalues[c1] == 2) 0; // do nothing
            // conflicting sides from two surfaces meeting at corner
            else if(std::abs(mvalues[c1]-param) < EPSSURF && svalues[c1] != side) svalues[c1] = 2;
            else svalues[c1] = side;

            mvalues[c1] = param;
          }

          if(mvalues[c2] < 0 || (1.0-param) <= mvalues[c2]) {
            if((1.0-param) == 0) svalues[c2] = 0;
            else if(svalues[c2] == 2) 0; // do nothing
            else if(std::abs(mvalues[c2]-(1.0-param)) < EPSSURF && svalues[c2] != !side) svalues[c2] = 2;
            else svalues[c2] = !side;

            mvalues[c2] = 1.0-param;
          }

        } // end "if" hitflag
      }// end "for" for surfaces
		}// end "for" for corners in cellfe
	}// end "for" for grid cells

  // now set in/out dependent on cell type
	// only set those where svalues < 0 to avoid
  // .. overwriting corner points on cell edges which is handled above
  int sval;
  int cxyz[3];
  for(int icell = 0; icell < grid->nlocal; icell++) {

    cl[0] = cells[icell].lo[0];
    cl[1] = cells[icell].lo[1];
    cl[2] = cells[icell].lo[2];
    xyzcell = get_cxyz(cxyz,cl);

    // itype = 1 - fully outside
    // itype = 2 - fully inside
    // itype = 3 - has surfaces
    // cannot just use types, if surface on corner
    // .. can be either 2 or 3 depending on which corner (ambiguity)
    itype = cinfo[icell].type;

    // fully inside so set all corner values to max
    if(itype==2) {
      sval = 1;
    // fully outside so set all corners to min
    } else if (itype==1) {
      sval = 0;
    } else {
      continue;
    }

    // set corners if not already set
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;
    xyzcell = get_corner(cxyz[0]+1, cxyz[1], cxyz[2]);
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;
    xyzcell = get_corner(cxyz[0], cxyz[1]+1, cxyz[2]);
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;
    xyzcell = get_corner(cxyz[0]+1, cxyz[1]+1, cxyz[2]);
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;

    xyzcell = get_corner(cxyz[0], cxyz[1], cxyz[2]+1);
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;
    xyzcell = get_corner(cxyz[0]+1, cxyz[1], cxyz[2]+1);
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;
    xyzcell = get_corner(cxyz[0], cxyz[1]+1, cxyz[2]+1);
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;
    xyzcell = get_corner(cxyz[0]+1, cxyz[1]+1, cxyz[2]+1);
    if(svalues[xyzcell] < 0) svalues[xyzcell] = sval;
  }

  // lastly handle ambiguous cases based on neighbors
  // .. which do not intersect with a surface (intersect)

  int filled = 0;
  int j; // test neighbor
  int attempt = 0;
  int cremain = 0;
  while(!filled) {
    cremain = 0;
    filled = 1;

    for(int i = 0; i < Nxyz; i++) {
      if(svalues[i] == 0 || svalues[i] == 1) continue;
      //printf("\ni: %i; svalues: %i\n", i, svalues[i]);

      // try x-neighbor
      j = i - 1;
      if(j >= 0 && ivalues[i][0] < 0) {
        svalues[i] = svalues[j];
        continue;
      }

      j = i + 1;
      if(j < Nxyz && ivalues[i][1] < 0) {
        svalues[i] = svalues[j];
        continue;
      }

      // try y-neighbor
      j = i - (nxyz[0]+1);
      if(j >= 0 && ivalues[i][2] < 0) {
        svalues[i] = svalues[j];
        continue;
      }

      j = i + (nxyz[0]+1);
      if(j < Nxyz && ivalues[i][3] < 0) {
        svalues[i] = svalues[j];
        continue;
      }

      // try z-neighbor
      j = i - (nxyz[0]+1)*(nxyz[1]+1);
      if(j >= 0 && ivalues[i][4] < 0) {
        svalues[i] = svalues[j];
        continue;
      }

      j = i + (nxyz[0]+1)*(nxyz[1]+1);
      if(j < Nxyz && ivalues[i][5] < 0) {
        svalues[i] = svalues[j];
        continue;
      }

      cremain++;
      filled = 0;
    }

    attempt++;
    if(attempt>20) break;

  }

  if(!filled) error->one(FLERR,"cannot find reference easily");

  // should be exactly same as 2D
  if(aveFlag) {
    int nval;
    double ivalsum;
	  for(int i = 0; i < Nxyz; i++) {
      ivalsum = 0.0;
      if(svalues[i] == 0) cvalues[i] = cout;
      else {
        nval = 0;
        for(int j = 0; j < npairs; j++) {
          if(ivalues[i][j] >= 0) {
            ivalsum += ivalues[i][j];
            nval++;
          }
        }

        // no intersections
        if(nval == 0) cvalues[i] = cin;
        // need to set these points as outside to avoid very small volume error
        else if(ivalsum == 0) cvalues[i] = MAX(thresh-1,cout);
        else {
          cvalues[i] = param2in(ivalsum/nval,0.0);
        }
      }

      if(cvalues[i] < 0 || cvalues[i] > 255)
        error->one(FLERR,"corner point out of range");
	  }// end "for" for grid cells

  } else {
    for(int i = 0; i < Nxyz; i++) {
      if(svalues[i] == 0) cvalues[i] = cout;
      else if(svalues[i] == 1) cvalues[i] = cin;
    }// end "for" for grid cells
  }

  // free up memory
  memory->destroy(ivalues);
  memory->destroy(mvalues);
  memory->destroy(svalues);

  //error->one(FLERR,"check");
	return;
}

/* ----------------------------------------------------------------------
	 Same as corner_hit2d but for 3d
------------------------------------------------------------------------- */

int Surf::corner_hit3d(double *p1, double *p2,
    Tri* tri, double &param, int &side, int &onsurf)
{
  onsurf = 0;

  // try intersect first
  int h, tside;
  double tparam;
  double d3dum[3];
  h = Geometry::line_tri_intersect(p1,p2,tri->p1,tri->p2,tri->p3,
      tri->norm,d3dum,tparam,tside);

  if(h) {
    if(tparam < EPSSURF || (1.0-tparam) < EPSSURF) onsurf = 1;
    if(tside == 1 || tside == 2 || tside == 5) {
      side = 1;
      param = tparam;
      return true;
    } else {
      side = 0;
      param = tparam;
      return true;
    }
  }

  // if miss, maybe surface very close to corner/edge
  // perturbed points
  double p1p[3];
  double p2p[3];

  double dx[26], dy[26], dz[26];
  double dp = mind/1000.0;
  dx[0] = dx[2] = dx[3] = dx[4] = 
    dx[15] = dx[16] = dx[18] = dx[23] = dx[24] = dp;
  dx[7] = dx[9] = dx[10] = dx[11] = 
    dx[14] = dx[17] = dx[19] = dx[22] = dx[25] = -dp;
  dx[1] = dx[5] = dx[6] = dx[8] = 
    dx[12] = dx[13] = dx[20] = dx[21] = 0;

  dy[0] = dy[1] = dy[3] = dy[5] = 
    dy[14] = dy[16] = dy[19] = dy[21] = dy[25] = dp;
  dy[7] = dy[8] = dy[10] = dy[12] = 
    dy[15] = dy[17] = dy[18] = dy[20] = dy[24] = -dp;
  dy[2] = dy[4] = dy[6] = dy[9] = 
    dy[11] = dy[13] = dy[22] = dy[23] = 0;

  dz[0] = dz[1] = dz[2] = dz[6] = 
    dz[14] = dz[15] = dz[17] = dz[20] = dz[22] = dp;
  dz[7] = dz[8] = dz[9] = dz[13] = 
    dz[16] = dz[18] = dz[19] = dz[21] = dz[23] = -dp;
  dz[3] = dz[4] = dz[5] = dz[10] = 
    dz[11] = dz[12] = dz[24] = dz[25] = 0;

  for(int i = 0; i < 26; i++) {
    p1p[0] = p1[0] + dx[i];
    p1p[1] = p1[1] + dy[i];
    p1p[2] = p1[2] + dz[i];

    p2p[0] = p2[0] + dx[i];
    p2p[1] = p2[1] + dy[i];
    p2p[2] = p2[2] + dz[i];
 
    h = Geometry::line_tri_intersect(p1p,p2p,tri->p1,tri->p2,tri->p3,
        tri->norm,d3dum,tparam,tside);
    if(h) {
      if(tside == 1 || tside == 2 || tside == 5) {
        side = 1;
        if(tparam<0.5) param = 0.0;
        else param = 1.0;
        return true;
      } else {
        side = 0;
        if(tparam<0.5) param = 0.0;
        else param = 1.0;
        return true;
      }
    }
  }

  // true miss
  return false;
}

/* ----------------------------------------------------------------------
	 Determines corner values given an explicit surface. Cvalues then used
	 later in ablate to create the implicit surfaces
------------------------------------------------------------------------- */

int Surf::get_cxyz(int *ic, double *lc)
{

  // find lower bounds
  double lo[3];
  lo[0] = domain->boxhi[0];
  lo[1] = domain->boxhi[1];
  lo[2] = domain->boxhi[2];

  // shift by lower bounds
  double lclo[3];
  for(int d = 0; d < 3; d++) {
    lclo[d] = lo[d] + lc[d];
    ic[d] = static_cast<int> (std::round(lclo[d] / xyzsize[d]));
  }

  int icell = get_corner(ic[0], ic[1], ic[2]);

  return icell;
}

/* ----------------------------------------------------------------------
	 Get cell from coordinates
------------------------------------------------------------------------- */

int Surf::get_cell(int icx, int icy, int icz)
{
  int icell;
  if(domain->dimension == 2) icell = icx + icy*nxyz[0];
  else icell = icx + icy*nxyz[0] + icz*nxyz[0]*nxyz[1];

  return icell;
}

/* ----------------------------------------------------------------------
	 Get corner values from coordinates
------------------------------------------------------------------------- */

int Surf::get_corner(int icx, int icy, int icz)
{
  int icell;
  if(domain->dimension == 2) icell = icx + icy*(nxyz[0]+1);
  else icell = icx + icy*(nxyz[0]+1) + icz*(nxyz[0]+1)*(nxyz[1]+1);

  return icell;
}

/* ----------------------------------------------------------------------
	 Get corner values from coordinates
------------------------------------------------------------------------- */

int Surf::get_corner(double dcx, double dcy, double dcz)
{
  // find lower bounds
  double lo[3];
  lo[0] = domain->boxhi[0];
  lo[1] = domain->boxhi[1];
  lo[2] = domain->boxhi[2];

  // shift by lower bounds
  double lclo[3];
  double ic[3];
  double lc[3];
  lc[0] = dcx;
  lc[1] = dcy; 
  lc[2] = dcz;
  for(int d = 0; d < 3; d++) {
    lclo[d] = lo[d] + lc[d];
    ic[d] = static_cast<int> (std::round(lclo[d] / xyzsize[d]));
  }

  int icell;
  if(domain->dimension == 2) icell = ic[0] + ic[1]*(nxyz[0]+1);
  else icell = ic[0] + ic[1]*(nxyz[0]+1) + ic[2]*(nxyz[0]+1)*(nxyz[1]+1);

  return icell;
}

/* ----------------------------------------------------------------------
   remove all lines in surf group
   condense data structures by removing deleted points & lines
------------------------------------------------------------------------- */

void Surf::remove_2d(int groupbit)
{
  int i;

  // remove lines in group
  Surf::Line *line;
  int nline = nsurf;
  int nbytes = sizeof(Surf::Line);

  int n = 0;
  for (i = 0; i < nline; i++) {
    if (lines[i].mask & groupbit) continue;
    if (i != n) memcpy(&lines[n],&lines[i],nbytes);
    n++;
  }
  nsurf = nlocal = n;

  // print stats after removal

  int nline_remove = nline - nsurf;

  if (comm->me == 0) {
    if (screen) {
      fprintf(screen,"  removed %d lines\n",nline_remove);
      fprintf(screen,"  " BIGINT_FORMAT " lines remain\n",nsurf);
    }
    if (logfile) {
      fprintf(logfile,"  removed %d lines\n",nline_remove);
      fprintf(logfile,"  " BIGINT_FORMAT " lines remain\n",nsurf);
    }
  }
}

/* ----------------------------------------------------------------------
   remove all triangles in surf group
   condense data structures by removing deleted points & triangles
------------------------------------------------------------------------- */

void Surf::remove_3d(int groupbit)
{
  int i;

  // remove triangles in group

  Surf::Tri *tris = surf->tris;
  int ntri = surf->nsurf;
  int nbytes = sizeof(Surf::Tri);

  int n = 0;
  for (i = 0; i < ntri; i++) {
    if (tris[i].mask & groupbit) continue;
    if (i != n) memcpy(&tris[n],&tris[i],nbytes);
    n++;
  }

  nsurf = nlocal = n;

  // print stats after removal

  int ntri_remove = ntri - nsurf;

  if (comm->me == 0) {
    if (screen) {
      fprintf(screen,"  removed %d tris\n",ntri_remove);
      fprintf(screen,"  " BIGINT_FORMAT " tris remain\n",nsurf);
    }
    if (logfile) {
      fprintf(logfile,"  removed %d tris\n",ntri_remove);
      fprintf(logfile,"  " BIGINT_FORMAT " tris remain\n",nsurf);
    }
  }
}
