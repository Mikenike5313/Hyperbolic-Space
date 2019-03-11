//Error: rounding errors cause points to not be exactly on hyperbola




//TODO: make it so more points can be added


//needed to concatonate arrays properly
Array.prototype.add = function(arr, modify, inReverse) {
	if(inReverse) {
		for(var i = arr.length-1; i >= 0; i--) {
			if(modify) {
				this.push(modify(arr[i]));
			}
			else {
				this.push(arr[i]);
			}
		}
	}
	else {
		for(var i = 0, len = arr.length; i < len; i++) {
			if(modify) {
				this.push(modify(arr[i]));
			}
			else {
				this.push(arr[i]);
			}
		}
	}
}


var es,
	esctx;
var hs,
	hsctx;

var n;
var basis;

var prePts; //vectors before graham schmidt
var u, //user chosen point on hyperboloid
	v; //calculated with u

var pu, //poincare u
	pv; //poincare v
var isGrabbingPt; //bool array storing whether or not point is being grabbed, [pu, pv]


var hyperboloidPoints = []; //used to plot hyperboloid


var mouseDown = false,
	mouseX,
	mouseY,
	preX,
	preY;

var scl;


//linear algebra functions

function transpose(m) {
	if(m.length <= 0 || m[0].length <= 0) {
		console.log('Input Error: Cannot transpose matrix:\n' + m);
	}
	var mT = [];
	for(var i = 0; i < m[0].length; i++) {
		mT.push([]);
		for(var j = 0; j < m.length; j++) {
			mT[i][j] = m[j][i];
		}
	}
	return mT;
}

function add(u, v) {
	if(u.length !== v.length) {
		console.log("Error: Vectors from different spaces.");
		return;
	}

	var dim = u.length || v.length;
	var s = [];
	for(var i = 0; i < dim; i++) {
		s[i] = u[i] + v[i];
	}

	return s;
}

function scale(l, v) {
	var u = [];
	for(var i = 0; i < v.length; i++) {
		u[i] = l*v[i];
	}
	return u;
}

function project(rn, m) {
	if(rn.length === m) { //if n = m, rn is part of rm already
		return rn;
	}
	m = (m) ? m : 1;
	var rm = [];
	for(var i = 0; i < m; i++) {
		rm[i] = rn[i] || 0;
	}
	return rm;
}

function linearTransform(x, t) { //t is a matrix, x is a vector
	if(!t || !x || t[0].length !== x.length) {
		console.log('InputError: Could not perform linear transformation:\n' + t + '\non:\n' + x);
		return;
	}

	var b = [];

	for(var i = 0; i < t.length; i++) {
		b[i] = 0;
		for(var j = 0; j < x.length; j++) {
			b[i] += t[i][j] * x[j];
		}
	}

	return b;
}

function polarToVector(r, angles) { //angles stored in this order: [p_x, p_yz, p_w, ...] (ex. 4D [p_x, p_yz, p_w])
	var dim = angles.length+1;
	var v = [];
	for(var i = 0, a; i < dim; i++) {
		a = (i > 1) || (i > angles.length-1) ? i-1 : i; //since second angle (index 1) is in zy-plane
		v[i] = (i === 2) ? r*Math.sin(angles[a]) : r*Math.cos(angles[a]); //z is given by the sin of zy-angle (y is given by cos of the same angle but this is covered already by the else)
		if(i !== 0) {
			v[i] *= Math.sin(angles[0]); //arbitrarily choose the x-axis to be the main axis (because hyperboloid is around it in this program)
			for(var o = a+1; o < dim-1; o++) {
				v[i] *= Math.sin(angles[o]); //multiply other coordinates by the sin of the angles in new dimensions to preserve length r
			}
		}
	}
	return v;
}

function grahamSchmidt(basis, innerProduct) {
	var orthonormalizedBasis = [];
	for(var b = 0; b < basis.length; b++) {
		orthonormalizedBasis[b] = basis[b];
		for(var i = 0; i < b; i++) {
			var projI = scale(innerProduct(orthonormalizedBasis[i], basis[b])/innerProduct(orthonormalizedBasis[i], orthonormalizedBasis[i]), orthonormalizedBasis[i]);
			orthonormalizedBasis[b] = add(orthonormalizedBasis[b], scale(-1, projI));
		}
		orthonormalizedBasis[b] = scale(1/Math.sqrt(Math.abs(innerProduct(orthonormalizedBasis[b], orthonormalizedBasis[b]))), orthonormalizedBasis[b]);
	}
	return orthonormalizedBasis;
}

//rotation
function rotate3D(v, ax, rad) { //v is the r3 vector, ax is the unit r3 vector of the axis, rad is radians rotated
	// http://ksuweb.kennesaw.edu/~plaval/math4490/rotgen.pdf
	//put into  ^ their ^  terminology
	var ux = ax[0],
		uy = ax[1],
		uz = ax[2];
	var c = Math.cos(rad),
		s = Math.sin(rad);
	var t = 1 - c;

	var rotationMatrix = [
		[t*ux*ux + c, t*ux*uy - s*uz, t*ux*uz + s*uy],
		[t*ux*uy + s*uz, t*uy*uy + c, t*uy*uz - s*ux],
		[t*ux*uz - s*uy, t*uy*uz + s*ux, t*uz*uz + c]
	];

	return linearTransform(v, rotationMatrix);
}


//hyperbola related functions

function hyperbolicBilinear(u, v) {
	if(u.length !== v.length) {
		console.log("Error: Vectors from different spaces.");
		return;
	}

	var dim = u.length || v.length;
	var innerProduct = u[0]*v[0];
	for(var i = 1; i < dim; i++) {
		innerProduct -= u[i]*v[i];
	}

	return innerProduct;
}

function projectToPoincare(p) { //projects point onto poincare disc/ball
	var pointcare = []; //play on words, but will be a vector representing the projected point
	for(var d = 1; d < p.length; d++) {
		pointcare[d-1] = p[d]/(1+p[0]);
	}
	return pointcare;
}

function backToHyperboloid(p) { //takes poincare point and projects it back onto the hyperboloid
	var hyp = [];

	var xNumerator = 1; //numerator for coordinate of dimension that hyperboloid extends into
	var denominator = 1; //denominator for all dimension coordinates
	for(var d = 0; d < p.length; d++) {
		var sqr = p[d]*p[d];
		xNumerator += sqr;
		denominator -= sqr;
	}

	hyp[0] = xNumerator/denominator;
	for(var d = 1; d <= p.length; d++) {
		hyp[d] = 2*p[d-1]/denominator;
	}

	return hyp;
}


//hyperboloid plotting functions

function generateAngleSamples(numSamples, min, max) { //[min, max)
	var angles = [];
	for(var ang = 0; ang < numSamples; ang++) {
		angles[ang] = ang*(max - min)/numSamples + min;
	}
	return angles;
}

function getHyperboloidPoint(angles) { //angles stored in this order: [p_x, p_yz, p_w, ...] (ex. 4D [p_x, p_yz, p_w])
	return polarToVector(Math.sqrt(1/(Math.cos(2*angles[0]))), angles);
}

function generateHyperboloidSamplePoints(dim, ptsPerRev) { //do not do a lot, algorithm is O(ptsPerRev*dim + ptsPerRev^dim-1)
	if(dim < 2) { //check if enough dimensions
		console.log("Error: Hyperbola cannot be constructed in less than 2 dimensions.");
		return;
	}


	//generate set of all possible angles
	var angleSet = generateAngleSamples(ptsPerRev, 0, Math.PI/4); //at theta = PI/4, length of vector from origin to point on hyperboloid goes to infinity, must prevent this (in this function, max is exclusive)
	//store angles so points can be generated, angles stored as 1D array, ptsPerRev angles for each dim-1

	//these only needed as dimensionality increases
	if(dim > 2) {
		//first do angle that covers 2 dimensions of motion
		var phi = generateAngleSamples(ptsPerRev, 0, 2*Math.PI);
		angleSet.add(phi);

		for(var a = 2; a < dim - 1; a++) { //1 dimension already covered by theta, and the 1 angle accounting for 2 dimensions is already covered above => only need dim-3 more
			var angleA = generateAngleSamples(ptsPerRev, 0, Math.PI);
			angleSet.add(angleA);	
		}
	}

	var samplePoints = [];

	var count = 0,
		max = Math.pow(ptsPerRev, dim-1);
	var start = Date.now();
	//var repeatPoints = []; //tracks whether or not points that would repeat (where p_i = 0, this doesn't occur when p_ij = 0, for example p_yx = 0 would not cause repeat points) have already been added, prevents unnecesary checks
	while(count < max) {
		var angles = [];
		for(var i = 0; i < dim-1; i++) {
			angles[i] = angleSet[i*ptsPerRev + Math.floor(count/Math.pow(ptsPerRev, dim-2-i))%ptsPerRev]; //traverse all combinations by counting up in base ptsPerRev up to ptsPerRev^dim-1
		}
		
		//TODO: implement this if possible, would also need to change how hyperbola is drawn
		//saves operations but makes it harder to draw the hyperbola
		/*
		if(angles[0] === 0) { //whenever theta = 0, vector is always [1, 0, 0, 0, 0, 0, 0, ...], checks for this to eliminate unnecesary operations (saves ptsPerRev^n-2 - 1 operations)
			if(repeatPoints.length > 0) {
				count++;
				continue;
			}
			else {
				repeatPoints[0] = true;
			}
		}
		//TODO: save more operations when other polar angles are 0
		//*/

		samplePoints.push(getHyperboloidPoint(angles));

		if(Date.now() - start > 60000) {
			alert("Error: operation too slow. Cancelling hyperboloid sample point computiation.");
			break;
		}
		count++;
	}

	if(dim === 2) { //include points reflected over x-axis when in only 2D x-y plane
		var orderedSamplePoints = [];
		orderedSamplePoints.add(samplePoints.slice(1), function(point) {
			var reflectedPoint = [point[0]];
			reflectedPoint.add(scale(-1, point.slice(1)));

			return reflectedPoint;
		}, true);
		orderedSamplePoints.add(samplePoints);
		return orderedSamplePoints;
	}
	return samplePoints;
}

function generateGeodesicSamplePoints(range, separation) { //generates geodesic sample points between u & v on the hyperboloid
	points = [];
	for(var w = -range; w <= range; w += separation) {
		points.push(add(scale(Math.cosh(w), u), scale(Math.sinh(w), v)));
	}
	return points;
}


//display functions

function dotHyperboloid(ctx, hypDim, ptsPerRev, color) {
	if(hyperboloidPoints.length === 0) { //TODO: add check to see if requested dimension of ppr changes
		hyperboloidPoints = generateHyperboloidSamplePoints(hypDim+1, ptsPerRev);
	}

	for(var p = 0; p < hyperboloidPoints.length; p++) {
		displayPoint(ctx, scale(scl, linearTransform(hyperboloidPoints[p], transpose(euBasis))), color);
	}
}

function fillQuadrilateral(ctx, pts, color) { //points must be in order [p1, p2, p3, p4]: p1 is "bottom left", p2 is "bottom right", p3 is "top left", p4 is "top right"
	//ensure quadrilateral is being drawn
	if(pts.length !== 4) {
		console.log("Error: shape is not a quadrilateral.");
		return;
	}
	//ensure points are in 2D space & have been placed in space properly (using our basis) before rendering
	var modPoints = [];
	for(var p = 0; p < 4;  p++) {
		modPoints[p] = project(scale(scl, linearTransform(pts[p], transpose(euBasis))), 2);
	}

	ctx.fillStyle = color || 'rgba(255, 255, 255, 0.5)';
	ctx.beginPath(); //here is why order matters in pts array
	ctx.moveTo(ctx.canvas.width/2 + modPoints[0][0], ctx.canvas.height/2 - modPoints[0][1]);
	ctx.lineTo(ctx.canvas.width/2 + modPoints[1][0], ctx.canvas.height/2 - modPoints[1][1]);
	ctx.lineTo(ctx.canvas.width/2 + modPoints[3][0], ctx.canvas.height/2 - modPoints[3][1]);
	ctx.lineTo(ctx.canvas.width/2 + modPoints[2][0], ctx.canvas.height/2 - modPoints[2][1]);
	ctx.closePath();
	ctx.fill();
}

function drawHyperboloid(ctx, hypDim, ptsPerRev, color) {
	if(hyperboloidPoints.length === 0) { //TODO: add check to see if requested dimension of ppr changes
		hyperboloidPoints = generateHyperboloidSamplePoints(hypDim+1, ptsPerRev);
	}

	if(hypDim < 1) { //0 or 1 D euclidian space
		console.log('Error: can\'t draw hyperboloid in less than 2 dimensions.');
		return;
	}
	if(hypDim === 1) { //2D euclidian space
		//ensure points are in 2D space & have been placed in space properly (using our basis) before rendering
		var modPoints = [];
		for(var p = 0; p < hyperboloidPoints.length; p++) {
			modPoints[p] = project(scale(scl, linearTransform(hyperboloidPoints[p], transpose(euBasis))), 2);
		}

		ctx.strokeStyle = color || 'white';
		ctx.beginPath();
		ctx.moveTo(ctx.canvas.width/2 + modPoints[0][0], ctx.canvas.height/2 - modPoints[0][1]);
		for(var i = 1; i < modPoints.length; i++) {
			ctx.lineTo(ctx.canvas.width/2 + modPoints[i][0], ctx.canvas.height/2 - modPoints[i][1]);
		}
		ctx.stroke();
		return;
	}

	//TODO: possibly change this if able, would need to also change how sample points are generated
	//right now it requires that there be repeat points
	//not sure if this current method generalizes to higher dimensions than hypN = 2, eN = 3
	for(var bl = 0; bl < hyperboloidPoints.length/4; bl++) { //each ql will be defined by its bottom left corner

	}

	for(var slice = 0; slice < ptsPerRev-1; slice++) { //increment up theta, must do this because bounds are different
		var bottom = slice,
			top = slice+1;
		//nth angle changes every ptsPerRev^hypDim-n
		var ptsPerSlice = Math.pow(ptsPerRev, hypDim-1); //a slice will be a set of all points with the same theta (first angle)

		for(var section = 0; section < ptsPerRev; section++) { //increment around phi, must do this because bounds are different
			var left = section,
				right = section+1 >= ptsPerRev ? 0 : section+1;

			//nth angle changes every ptsPerRev^hypDim-n
			var ptsPerSection = Math.pow(ptsPerRev, hypDim-2);

			if(hypDim === 2) {
				fillQuadrilateral(ctx, [hyperboloidPoints[bottom*ptsPerSlice + left*ptsPerSection], hyperboloidPoints[bottom*ptsPerSlice + right*ptsPerSection], hyperboloidPoints[top*ptsPerSlice + left*ptsPerSection], hyperboloidPoints[top*ptsPerSlice + right*ptsPerSection]], color);
			}

			if(hypDim > 2) {
				//TODO: implement higher dimensional viewer
				//would it even have meaning?

				//general order (i think): fix outmost variable, vary innermost variable from start (1st point) to the next (2nd point), vary the next out variable once & reset the inner (3rd point), vary the inner variable (4th point)
				//							(in this case each variable is an angle that can be varied, corresponding to dimensions of movement => n-1 variables for n dimensional euclidian space)
				//							=> can be viewed as counting in binary

				//start at a given point and count up in binary to 2^n-1 - 1 (starting at 0, where 0 would be the first point)
				//this process will yield 1 section filled on the hyperboloid (ex. for a 3d hyperboloid, 1 quadrilateral would be constructed)
				
				dotHyperboloid(ctx, hypDim, ptsPerRev, color); //just do dot hyperboloid for time being
				return;
			}
		}

	}
}

function drawHyperboloidGeodesic(ctx, color) { //draws geodesic between u & v on hyperboloid
	var points = generateGeodesicSamplePoints(100, 0.1);
	for(var p = 0; p < points.length; p++) {
		points[p] = scale(scl, linearTransform(points[p], transpose(euBasis)));
	}
	drawLine(ctx, points, color);
}

function drawPoincareGeodesic(ctx, color) {
	var points = generateGeodesicSamplePoints(100, 0.1);
	for(var p = 0; p < points.length; p++) {
		points[p] = scale(scl, projectToPoincare(points[p]));
	}
	drawLine(ctx, points, color);
}


function displayPoint(ctx, v, color) {
	var r2 = project(v, 2);
	ctx.fillStyle = color || 'white';
	ctx.fillRect(r2[0]-2 + ctx.canvas.width/2, -r2[1]-2 + ctx.canvas.height/2, 4, 4);
}

function drawLine(ctx, points, color) {
	for(var p = 0; p < points.length; p++) {
		points[p] = project(points[p], 2);
	}
	ctx.strokeStyle = color || "white";
	ctx.beginPath();
	ctx.moveTo(points[0][0]+ctx.canvas.width/2, -points[0][1]+ctx.canvas.height/2);
	for(var p = 1; p < points.length; p++) {
		ctx.lineTo(points[p][0]+ctx.canvas.width/2, -points[p][1]+ctx.canvas.height/2);
	}
	ctx.stroke();
}

function displayVector(ctx, v, color) {
	var r2 = project(v, 2);
	//line
	ctx.strokeStyle = color || 'white';
	ctx.beginPath();
	ctx.moveTo(ctx.canvas.width/2, ctx.canvas.height/2);
	ctx.lineTo(r2[0] + ctx.canvas.width/2, -r2[1] + ctx.canvas.height/2);
	ctx.stroke();

	//tip
	displayPoint(ctx, r2, color);
}

function displayBasis(basis, ctx) {
	var colorChange = 360/basis.length;
	for(var b = 0; b < basis.length; b++) {
		var color = b*colorChange;
		displayVector(ctx, scale(Math.min(ctx.canvas.width, ctx.canvas.height)/2 - 3, basis[b]), 'hsl(' + color + ', 100%, 50%)');
		displayVector(ctx, scale(Math.min(ctx.canvas.width, ctx.canvas.height)/2 - 3, scale(-1, basis[b])), 'hsl(' + color + ', 100%, 20%)');
	}
}

function displayES() {
	esctx.clearRect(0, 0, es.width, es.height);

	displayBasis(euBasis, esctx);
	drawHyperboloid(esctx, n, 20);
	displayVector(esctx, scale(scl, linearTransform(u, transpose(euBasis))), 'purple'); //u
	displayVector(esctx, scale(scl, linearTransform(prePts[1], transpose(euBasis))), 'yellow'); //v before graham schmidt process
	//displayVector(esctx, scale(scl, linearTransform(v, transpose(euBasis))), 'orange'); //v
	drawHyperboloidGeodesic(esctx, "pink");
}

function displayHS() {
	hsctx.clearRect(0, 0, es.width, es.height);
	if(n == 2) {
		hsctx.strokeStyle = "white";
		hsctx.beginPath();
		hsctx.arc(hsctx.canvas.width/2, hsctx.canvas.height/2, scl, 0, 2*Math.PI);
		hsctx.stroke();
	}
	//TODO: implement for higher hyperbolic dimensions
	//			ex. if n=3 make a rotation thing to rotate around the poincare ball
	drawPoincareGeodesic(hsctx, "pink");
	displayPoint(hsctx, scale(scl, pu), "purple");
	displayPoint(hsctx, scale(scl, pv), "yellow");
}


//ui functions

function resize() {
	es.width = es.offsetWidth;
	es.height = es.offsetHeight;

	hs.width = hs.offsetWidth;
	hs.height = hs.offsetHeight;
}


//startup
function initRandomHyperboloidPoints() {
	prePts = [];
	for(var i = 0; i < 2; i++) {
		var angles = [];
		if(n < 1) {
			console.log('Error: dimension of hyperbolic manifold cannot be less than 1.');
			return;
		}
		else if(n === 1) {
			angles[0] = Math.random()*(Math.PI/2) - Math.PI/4;
		}
		else if(n > 1) {
			angles[0] = Math.random()*Math.PI/4;
			angles[1] = Math.random()*2*Math.PI;
			for(var a = 2; a < n; a++) {
				angles[a] = Math.random()*Math.PI;
			}
		}

		prePts[i] = getHyperboloidPoint(angles);
	}
}
function initPoints() {
	var planeBasis = grahamSchmidt(prePts, hyperbolicBilinear);

	u = planeBasis[0];
	v = planeBasis[1];

	pu = projectToPoincare(u);
	pv = projectToPoincare(prePts[1]);
}

function init() {
	es = document.getElementById('euclidianN+1Space');
	esctx = es.getContext('2d');

	hs = document.getElementById('hyperbolicNSpace');
	hsctx = hs.getContext('2d');

	resize();

	scl = Math.min(esctx.canvas.width, esctx.canvas.height)/4 - 3;

	n = 2; //hyperbolic dimension constant

	euBasis = [];
	for(var i = 0; i < n+1; i++) {
		var b = [];
		for(var j = 0; j < n+1; j++) {
			var bj = (j === i) ? 1 : 0;
			b.push(bj);
		}
		euBasis.push(b);
	}

	//pick 2 random points on hyperboloid & init plane basis
	initRandomHyperboloidPoints();
	initPoints();
	

	if(n === 2) { //rotation math only works for 3d simulation, interactive u & v on the poincare disk only works if n = 2
		es.addEventListener('mousedown', function(event) {
			mouseDown = true;
			preX = window.pageXOffset-es.offsetLeft + event.clientX - es.width/2,
			preY = -(window.pageYOffset-es.offsetTop + event.clientY - es.height/2);
		});
		es.addEventListener('mousemove', function(event) {
			mouseX = window.pageXOffset-es.offsetLeft + event.clientX - es.width/2,
			mouseY = -(window.pageYOffset-es.offsetTop + event.clientY - es.height/2);
			if(mouseDown) {

			    //r needs to enclose points on canvas, or cosAng will be > 1 => BAD
				//ERROR: for some reason when cosAng = 1, the system breaks, added check below

				var curX = mouseX,
					curY = mouseY;

				var r = (es.width/2)*(es.width/2) + (es.height/2)*(es.height/2) + 1; //ensure no point on canvas is outside of radius
				//get previous rotation start '3d' coordinates
				var px = preX,
					py = preY;
				var pz = Math.sqrt(r - px*px - py*py); //calc z

			    //get current '3d' coordinates
			    var cx = curX,
			        cy = curY;
			    var cz = Math.sqrt(r - cx*cx - cy*cy); //calc z

			    //make sure to update
			    preX = curX;
			    preY = curY;


			    var cosAng = (px*cx + py*cy + pz*cz)/r;

			    var rotAng = Math.acos(cosAng);
			    var axis = scale(1/(r*Math.sin(rotAng)), [py*cz - pz*cy, pz*cx - px*cz, px*cy - py*cx]);


			    //make sure cosAng is within range, if not, don't rotate
			    if(cosAng >= 1 || cosAng <= -1) {
			      return;
			    }

			    //rotate
			    euBasis[0] = rotate3D(euBasis[0], axis, rotAng);
			    euBasis[1] = rotate3D(euBasis[1], axis, rotAng);
			    euBasis[2] = rotate3D(euBasis[2], axis, rotAng);

				displayES();
			}
		});
		es.addEventListener('mouseup', function() {
			mouseDown = false;
			preX = null;
			preY = null;
		});
		es.addEventListener('mouseout', function() {
			mouseDown = false;
			preX = null;
			preY = null;
		});
		//
		hs.addEventListener('mousedown', function(event) {
			mouseDown = true;
			preX = window.pageXOffset-hs.offsetLeft + event.clientX - hs.width/2,
			preY = -(window.pageYOffset-hs.offsetTop + event.clientY - hs.height/2);
		});
		hs.addEventListener('mousemove', function(event) {
			mouseX = window.pageXOffset-hs.offsetLeft + event.clientX - hs.width/2,
			mouseY = -(window.pageYOffset-hs.offsetTop + event.clientY - hs.height/2);
			var delX = (mouseX-preX)/scl,
				delY = (mouseY-preY)/scl;
			if((Math.round(16*mouseX/scl) == Math.round(16*project(pu, 2)[0]) && Math.round(16*mouseY/scl) == Math.round(16*project(pu, 2)[1]) && (isGrabbingPt === -1 || isGrabbingPt === undefined)) || isGrabbingPt === 0) { //mouse over u, *16 to give the mouse a range over which point is grabbable
				hs.style.cursor = "pointer";
				if(mouseDown) {
					isGrabbingPt = 0;
					//n = 2, so:
					if((pu[0] + delX)*(pu[0] + delX) + (pu[1] + delY)*(pu[1] + delY) <= 1) {
						pu[0] += delX;
						pu[1] += delY;
					}

					prePts[0] = backToHyperboloid(pu);
					initPoints();

					preX = mouseX;
					preY = mouseY;

					displayES();
					displayHS();
				}
			}
			else if((Math.round(16*mouseX/scl) == Math.round(16*project(pv, 2)[0]) && Math.round(16*mouseY/scl) == Math.round(16*project(pv, 2)[1]) && (isGrabbingPt === -1 || isGrabbingPt === undefined)) || isGrabbingPt === 1) { //mouse over v, *16 to give the mouse a range over which point is grabbable
				hs.style.cursor = "pointer";
				if(mouseDown) {
					isGrabbingPt = 1;
					//n = 2, so:
					if((pv[0] + delX)*(pv[0] + delX) + (pv[1] + delY)*(pv[1] + delY) <= 1) {
						pv[0] += delX;
						pv[1] += delY;
					}

					prePts[1] = backToHyperboloid(pv);
					initPoints();

					preX = mouseX;
					preY = mouseY;

					displayES();
					displayHS();
				}
			}
			else {
				hs.style.cursor = "default";
			}
		});
		hs.addEventListener('mouseup', function() {
			mouseDown = false;
			isGrabbingPt = -1;
		});
		hs.addEventListener('mouseout', function() {
			mouseDown = false;
		});
	}

	displayES();
	displayHS();
}

init();


function testHyperbolaPoints() {
	var bad = [];
	for(var p = 0; p < hyperboloidPoints.length; p++) {
		var result = hyperboloidPoints[p][0]*hyperboloidPoints[p][0];
		for(var i = 1; i < hyperboloidPoints[p].length; i++) {
			result -= hyperboloidPoints[p][i]*hyperboloidPoints[p][i];
		}
		if(result !== 1) {
			bad.push(p);
		}
	}
	return bad;
}
