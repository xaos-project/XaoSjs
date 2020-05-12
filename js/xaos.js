/*
 * XaoS.js
 * https://github.com/jblang/XaoS.js
 *
 * Copyright (C)2011 John B. Langston III
 * Copyright (C)2001, 2010 Andrea Medeghini
 * Copyright (C)1996, 1997 Jan Hubicka and Thomas Marsh
 *
 * Based on code from XaoS by Jan Hubicka (http://xaos.sf.net)
 * and from JAME by Andrea Medeghini (http://www.fractalwalk.net)
 *
 * This file is part of XaoS.js.
 *
 * XaoS.js is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * XaoS.js is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with XaoS.js.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
var xaos = xaos || {};

xaos.zoom = (function() {
    "use strict";

    const USE_XAOS = true;            // Whether to use zooming or recalculate every frame
    const USE_SYMMETRY = true;        // Whether to use symmetry when possible
    const USE_SOLIDGUESS = true;      // Whether to use solid guessing to avoid calculations
    const RANGES = 2;                 // Number of ranges to use for sizing approximation data
    const RANGE = 4;                  // Maximum distance to use for approximation
    const MASK = 0x7;                 // Mask value for maximum potential source lines
    const DSIZE = (RANGES + 1);       // Shift value for target lines
    const FPMUL = 64;                 // Multiplication factor for fixed-point representation
    const FPRANGE = FPMUL * RANGE;    // Fixed point range of approximation
    const MAX_PRICE = Number.MAX_VALUE;   // Maximum price of uninitialized approximation
    const NEW_PRICE = FPRANGE * FPRANGE;  // Price of calculating a new line
    const GUESS_RANGE = 4;                // Range to use for solid guessing

    /** A price entry in the approximation table
     * @constructor
     */
    function Price() {
        this.previous = null;       // Previous price calculated for the same line
        this.index = 0;             // Index of the source for this approximation (-1 means new calculation)
        this.price = MAX_PRICE;     // Price calculated for this line
    }

    /** A group of pixels to be moved
     * @constructor
     */
    function Move() {
        this.length = 0;            // number of pixels to move
        this.from = 0;              // starting offset of pixel source
        this.to = 0;                // starting offset of pixel destination
    }

    /** A single row or column of pixels in the image
     * @constructor
     */
    function Line() {
        this.recalculate = false;   // whether to recalculate this line
        this.dirty = false;         // whether this line needs to be redrawn
        this.isRow = false;         // whether this is a row (true) or column (false)
        this.index = 0;             // index of row or column within the image
        this.symIndex = 0;          // index of pixels to use for symmetry
        this.symTo = 0;             // position of pixels this is symmetrical to
        this.symRef = 0;            // position of pixels referring to this one
        this.oldPosition = 0.0;     // line's old position in the fractal's complex plane
        this.newPosition = 0.0;     // line's new position in the fractal's complex plane
        this.priority = 0.0;        // calculation priority for this row/column
    }

    /** An image derived from an HTML5 canvas
     * @param canvas - the canvas used to display the image
     * @constructor
     */
    function CanvasImage(canvas) {
        let width = canvas.clientWidth;
        let height = canvas.clientHeight;
        if (canvas.width !== width || canvas.height !== height) {
            canvas.width = width;
            canvas.height = height;
        } else {
            ctx.clearRect(0, 0, width, height);
        }

        this.canvas = canvas;
        this.context = canvas.getContext("2d");
        this.width = canvas.width;
        this.height = canvas.height;
        this.newImageData = this.context.createImageData(this.width, this.height);
        this.oldImageData = this.context.createImageData(this.width, this.height);
        this.newBuffer = new Uint32Array(this.newImageData.data.buffer);
        this.oldBuffer = new Uint32Array(this.oldImageData.data.buffer);
    }

    /** Swap new and old buffers */
    CanvasImage.prototype.swapBuffers = function() {
        var tmp = this.oldBuffer;
        this.oldBuffer = this.newBuffer;
        this.newBuffer = tmp;
        tmp = this.oldImageData;
        this.newImageData = this.oldImageData;
        this.oldImageData = tmp;
    };

    /** Draw the current image */
    CanvasImage.prototype.paint = function() {
        this.context.putImageData(this.newImageData, 0, 0);
    };

    /** Utility function to make an array of the specified size
     * with the specified initial value. It will do the right thing
     * to create unique items, whether you pass in a prototype, a
     * constructor, or a primitive.
     * @param {number} size - the size of the array.
     * @param initial - the initial value for each entry.
     */
    function makeArray(size, initial) {
        var i, data = [];
        for (i = 0; i < size; i++) {
            if (typeof initial === "object") {
                // prototype object
                data[i] = Object.create(initial);
            } else if (typeof initial === "function") {
                // constructor
                data[i] = new initial();
            } else {
                // primitive
                data[i] = initial;
            }
        }
        return data;
    }

    /** Container for all zoom context data for a particular canvas.
     *
     * @param image {CanvasImage} Image on which to draw the fractal.
     * @param fractal {FractalContext} Fractal parameters.
     * @constructor
     */
    function ZoomContext(image, fractal) {
        var size = Math.max(image.width, image.height);
        this.image = image;                                 // the image to draw the fractal on
        this.fractal = fractal;                             // the fractal formula used for the image
        this.columns = makeArray(image.width, Line);        // columns in the fractal image
        this.rows = makeArray(image.height, Line);          // rows in the fractal image
        this.sourcePos = makeArray(size + 1, 0);            // fixed-point positions for source lines
        this.oldBest = makeArray(size, null);               // best prices for previous line
        this.newBest = makeArray(size, null);               // best prices for current line
        this.calcPrices = makeArray(size, Price);           // prices for calculating new lines
        this.movePrices = makeArray(size << DSIZE, Price);  // prices for approximating new lines from exsiting ones
        this.moveTable = makeArray(image.width + 1, Move);  // table of pixels to be moved
        this.fillTable = makeArray(image.width + 1, Move);  // table of pixels to be filled
        this.queue = makeArray(image.width + image.height, null);   // queue of lines to calculate
        this.queueLength = 0;                               // length of the calculation queue
        this.startTime = 0;                                 // time that the current frame was started
        this.minFPS = 60;                                   // target FPS to maintain
        this.fudgeFactor = 0;                               // fudge factor used to achieve target FPS
        this.incomplete = false;                            // flag indicates incomplete calculation
        this.zooming = false;                               // flag indicates image is currently zooming
    }

    /** Swaps the old and new best prices in the this container. */
    ZoomContext.prototype.swapBest = function() {
        var tmpBest = this.oldBest;
        this.oldBest = this.newBest;
        this.newBest = tmpBest;
    };

    /** Convert fractal viewport from radius and center to x and y start to end ranges */
    ZoomContext.prototype.convertArea = function() {
        var radius = this.fractal.region.radius;
        var center = this.fractal.region.center;
        var aspect = this.image.width / this.image.height;
        var size = Math.max(radius.x, radius.y * aspect);
        return {
            begin: {
                x: center.x - size / 2,
                y: (center.y - size / 2) / aspect
            },
            end: {
                x: center.x + size / 2,
                y: (center.y + size / 2) / aspect
            }
        };
    };

    /** Resets line of pixels for fresh calculation
     *
     * @param line - row or column of pixels
     * @param begin - starting fractal cooridnate
     * @param end - ending coordinate
     * @param isRow - whether this is a row or column
     * @returns {number}
     */
    ZoomContext.prototype.initialize = function(lines, begin, end, isRow) {
        var i; 
        var p;
        var step = (end - begin) / lines.length;
        var line = null;

        for (i = 0, p = begin; i < lines.length; i++, p += step) {
            line = lines[i]
            line.recalculate = true;
            line.dirty = true;
            line.isRow = isRow;
            line.index = i;
            line.oldPosition = p;
            line.newPosition = p;
            line.symIndex = i;
            line.symTo = -1;
            line.symRef = -1;
        }
        return step;
    }

    /** Calculate price of approximating one line from another
     *
     * @param p1 - position of first line
     * @param p2 - position of second line
     * @returns {number} - price of approximation
     */
    function calcPrice(p1, p2) {
        return (p1 - p2) * (p1 - p2);
    }

    /** Calculate fixed-point representation of each line's old position
     * @param lines - lines to use for calculation
     * @param begin - beginning of floating point range
     * @param end - end of floating point range
     */
    ZoomContext.prototype.calcFixedpoint = function(lines, begin, end) {
        var tofix = (lines.length * FPMUL) / (end - begin);
        var i;
        this.sourcePos[lines.length] = Number.MAX_VALUE;
        for (i = lines.length - 1; i >= 0; i--) {
            this.sourcePos[i] = ((lines[i].oldPosition - begin) * tofix) | 0;
            if (this.sourcePos[i] > this.sourcePos[i + 1]) {
                this.sourcePos[i] = this.sourcePos[i + 1];
            }
        }
    }

    /** Choose the best approximation for lines based on previous frame
     *
     * @param lines - relocation table for rows or columns
     * @param begin - beginning coordinate (x or y)
     * @param end - ending coordinate (x or y)
     * @param newPosition - array of newPosition coordinates on the complex plane
     * @returns {number}
     */
    ZoomContext.prototype.approximate = function(lines, begin, end) {
        var previous = null;    // pointer to previous approximation
        var best = null;        // pointer to best approximation
        var line = null;        // pointer to current line
        var price = 0;          // price of current approximation
        var dest;               // index of the current destination line
        var idealPos = 0;       // ideal position for the current destination
        var maxPos = 0;         // maximum valid source position of the current destination
        var source = 0;         // index of current source line
        var prevBegin = 0;      // index of first potential source for current destination
        var prevEnd = 0;        // index of last potential source for current destination
        var currBegin = 0;      // index of first potential source for next destination
        var flag = 0;
        var size = lines.length;
        var step = (end - begin) / size;
        var sourcePos = this.sourcePos;

        // Calculate fixed-point positions of all source lines
        this.calcFixedpoint(lines, begin, end);

        for (dest = 0, idealPos = 0; dest < size; dest++, idealPos += FPMUL) {
            this.swapBest();
            maxPos = idealPos - FPRANGE;
            if (maxPos < -FPMUL) {
                maxPos = -FPMUL;
            }
            source = prevBegin;
            while (sourcePos[source] < maxPos) {
                source++;
            }
            currBegin = source;
            maxPos = idealPos + FPRANGE;

            // Find the previous approximation
            if ((prevBegin !== prevEnd) && (source > prevBegin)) {
                // Previous line had approximations; use them
                if (source < prevEnd) {
                    previous = this.oldBest[source - 1];
                } else {
                    previous = this.oldBest[prevEnd - 1];
                }
                price = previous.price;
            } else if (dest > 0) {
                // Previous line had no approximations
                // Use the price of calculating the previous line
                previous = this.calcPrices[dest - 1];
                price = previous.price;
            } else {
                // We're on the first line; no previous prices exists
                previous = null;
                price = 0;
            }

            // Add the price for calculating this line
            price += NEW_PRICE;
            best = this.calcPrices[dest];
            best.price = price;
            best.index = -1;
            best.previous = previous;

            // Try all possible approximations for this line and calculate the best one
            if (prevBegin !== prevEnd) {
                if (source === prevBegin) {
                    // We're on the first line so there is no previous line
                    if (sourcePos[source] !== sourcePos[source + 1]) {
                        previous = this.calcPrices[dest - 1];
                        price = previous.price + calcPrice(sourcePos[source], idealPos);
                        if (price < best.price) {
                            best = this.movePrices[(source << DSIZE) + (dest & MASK)];
                            best.price = price;
                            best.index = source;
                            best.previous = previous;
                        }
                    }
                    this.newBest[source++] = best;
                }
                previous = null;

                // Potential sources for the previous and current line overlap within
                // this range, so we have to calculate every possibility and find the best 
                while (source < prevEnd) {
                    if (sourcePos[source] !== sourcePos[source + 1]) {
                        previous = this.oldBest[source - 1];
                        price = previous.price + NEW_PRICE;
                        if (price < best.price) {
                            best = this.movePrices[((source - 1) << DSIZE) + (dest & MASK)];
                            best.price = price;
                            best.index = -1;
                            best.previous = previous;
                            this.newBest[source - 1] = best;
                        }
                        price = previous.price + calcPrice(sourcePos[source], idealPos);
                        if (price < best.price) {
                            best = this.movePrices[(source << DSIZE) + (dest & MASK)];
                            best.price = price;
                            best.index = source;
                            best.previous = previous;
                        } else if (sourcePos[source] > idealPos) {
                            this.newBest[source++] = best;
                            break;
                        }
                    }
                    this.newBest[source++] = best;
                }

                // We are past the overlapping area
                if (source > prevBegin) {
                    previous = this.oldBest[source - 1];
                } else {
                    previous = this.calcPrices[dest - 1];
                }
                price = previous.price + NEW_PRICE;
                if ((price < best.price) && (source > currBegin)) {
                    best = this.movePrices[((source - 1) << DSIZE) + (dest & MASK)];
                    best.price = price;
                    best.index = -1;
                    best.previous = previous;
                    this.newBest[source - 1] = best;
                }
                while (sourcePos[source] < maxPos) {
                    if (sourcePos[source] !== sourcePos[source + 1]) {
                        price = previous.price + calcPrice(sourcePos[source], idealPos);
                        if (price < best.price) {
                            best = this.movePrices[(source << DSIZE) + (dest & MASK)];
                            best.price = price;
                            best.index = source;
                            best.previous = previous;
                        } else if (sourcePos[source] > idealPos) {
                            break;
                        }
                    }
                    this.newBest[source++] = best;
                }
                while (sourcePos[source] < maxPos) {
                    this.newBest[source++] = best;
                }
            } else if (sourcePos[source] < maxPos) {
                if (dest > 0) {
                    previous = this.calcPrices[dest - 1];
                    price = previous.price;
                } else {
                    previous = null;
                    price = 0;
                }
                while (sourcePos[source] < maxPos) {
                    if (sourcePos[source] !== sourcePos[source + 1]) {
                        price += calcPrice(sourcePos[source], idealPos);
                        if (price < best.price) {
                            best = this.movePrices[(source << DSIZE) + (dest & MASK)];
                            best.price = price;
                            best.index = source;
                            best.previous = previous;
                        } else if (sourcePos[source] > idealPos) {
                            break;
                        }
                    }
                    this.newBest[source++] = best;
                }
                while (sourcePos[source] < maxPos) {
                    this.newBest[source++] = best;
                }

            }
            prevBegin = currBegin;
            currBegin = prevEnd;
            prevEnd = source;
        }
        if ((begin > lines[0].oldPosition) && (end < lines[size - 1].oldPosition)) {
            flag = 1;
        }
        if ((sourcePos[0] > 0) && (sourcePos[size - 1] < (size * FPMUL))) {
            flag = 2;
        }
        for (dest = size - 1; dest >= 0; dest--) {
            line = lines[dest]
            line.symTo = -1;
            line.symRef = -1;
            if (best.index < 0) {
                line.recalculate = true;
                line.dirty = true;
                line.symIndex = line.index;
            } else {
                line.symIndex = best.index;
                line.newPosition = lines[best.index].oldPosition;
                line.recalculate = false;
                line.dirty = false;
            }
            best = best.previous;
        }
        newPositions(lines, begin, end, step, flag);
        return step;
    }

    /** Choose new positions for lines based on calculated prices
     *
     * @param lines
     * @param size
     * @param begin1
     * @param end1
     * @param step
     * @param newPosition
     * @param flag
     */
    function newPositions(lines, begin1, end1, step, flag) {
        var delta = 0;
        var size = lines.length;
        var begin = 0;
        var end = 0;
        var s = -1;
        var e = -1;
        if (begin1 > end1) {
            begin1 = end1;
        }
        while (s < (size - 1)) {
            e = s + 1;
            if (lines[e].recalculate) {
                while (e < size) {
                    if (!lines[e].recalculate) {
                        break;
                    }
                    e++;
                }
                if (e < size) {
                    end = lines[e].newPosition;
                } else {
                    end = end1;
                }
                if (s < 0) {
                    begin = begin1;
                } else {
                    begin = lines[s].newPosition;
                }
                if ((e === size) && (begin > end)) {
                    end = begin;
                }
                if ((e - s) === 2) {
                    delta = (end - begin) * 0.5;
                } else {
                    delta = (end - begin) / (e - s);
                }
                switch (flag) {
                    case 1:
                        for (s++; s < e; s++) {
                            begin += delta;
                            lines[s].newPosition = begin;
                            lines[s].priority = 1 / (1 + (Math.abs((lines[s].oldPosition - begin)) * step));
                        }
                        break;
                    case 2:
                        for (s++; s < e; s++) {
                            begin += delta;
                            lines[s].newPosition = begin;
                            lines[s].priority = Math.abs((lines[s].oldPosition - begin)) * step;
                        }
                        break;
                    default:
                        for (s++; s < e; s++) {
                            begin += delta;
                            lines[s].newPosition = begin;
                            lines[s].priority = 1.0;
                        }
                        break;
                }
            }
            s = e;
        }
    }

    /** Populate symmetry data into relocation table
     *
     * @param lines
     * @param symi
     * @param symPosition
     * @param step
     */
    function prepareSymmetry(lines, symi, symPosition, step) {
        var i;
        var j = 0;
        var tmp;
        var abs;
        var distance;
        var newPosition;
        var size = lines.length;
        var max = size - RANGE - 1;
        var min = RANGE;
        var istart = 0;
        var line = null;
        var otherLine = null;
        var symj = (2 * symi) - size;
        symPosition *= 2;
        if (symj < 0) {
            symj = 0;
        }
        distance = step * RANGE;
        for (i = symj; i < symi; i++) {
            line = lines[i];
            if (line.symTo !== -1) {
                continue;
            }
            newPosition = line.newPosition;
            line.symTo = (2 * symi) - i;
            if (line.symTo > max) {
                line.symTo = max;
            }
            j = ((line.symTo - istart) > RANGE) ? (-RANGE) : (-line.symTo + istart);
            if (line.recalculate) {
                while ((j < RANGE) && ((line.symTo + j) < (size - 1))) {
                    tmp = symPosition - lines[line.symTo + j].newPosition;
                    abs = Math.abs(tmp - newPosition);
                    if (abs < distance) {
                        if (((i === 0) || (tmp > lines[i - 1].newPosition)) && (tmp < lines[i + 1].newPosition)) {
                            distance = abs;
                            min = j;
                        }
                    } else if (tmp < newPosition) {
                        break;
                    }
                    j++;
                }
            } else {
                while ((j < RANGE) && ((line.symTo + j) < (size - 1))) {
                    if (line.recalculate) {
                        tmp = symPosition - lines[line.symTo + j].newPosition;
                        abs = Math.abs(tmp - newPosition);
                        if (abs < distance) {
                            if (((i === 0) || (tmp > lines[i - 1].newPosition)) && (tmp < lines[i + 1].newPosition)) {
                                distance = abs;
                                min = j;
                            }
                        } else if (tmp < newPosition) {
                            break;
                        }
                    }
                    j++;
                }
            }
            line.symTo += min;
            otherLine = lines[line.symTo];
            if ((min === RANGE) || (line.symTo <= symi) || (otherLine.symTo !== -1) || (otherLine.symRef !== -1)) {
                line.symTo = -1;
                continue;
            }
            if (!line.recalculate) {
                line.symTo = -1;
                if ((otherLine.symTo !== -1) || !otherLine.recalculate) {
                    continue;
                }
                otherLine.symIndex = line.symIndex;
                otherLine.symTo = i;
                istart = line.symTo - 1;
                otherLine.recalculate = false;
                otherLine.dirty = true;
                line.symRef = line.symTo;
                otherLine.newPosition = symPosition - line.newPosition;
            } else {
                if (otherLine.symTo !== -1) {
                    line.symTo = -1;
                    continue;
                }
                line.symIndex = otherLine.symIndex;
                istart = line.symTo - 1;
                line.recalculate = false;
                line.dirty = true;
                otherLine.symRef = i;
                line.newPosition = symPosition - otherLine.newPosition;
            }
        }
    }

    /** Optimized array copy using Duff's Device.
     *
     * @param from {Array} source array
     * @param fromOffset {number} offset into source array
     * @param to {Array} idealPos array
     * @param toOffset {number} offset into idealPos array
     * @param length {number} elements to copy
     */
    function arrayCopy(from, fromOffset, to, toOffset, length) {
        var n = length % 8;
        while (n--) {
            to[toOffset++] = from[fromOffset++];
        }
        n = (length / 8) | 0;
        while (n--) {
            to[toOffset++] = from[fromOffset++];
            to[toOffset++] = from[fromOffset++];
            to[toOffset++] = from[fromOffset++];
            to[toOffset++] = from[fromOffset++];
            to[toOffset++] = from[fromOffset++];
            to[toOffset++] = from[fromOffset++];
            to[toOffset++] = from[fromOffset++];
            to[toOffset++] = from[fromOffset++];
        }
    }

    /** Apply previously calculated symmetry to image */
    ZoomContext.prototype.doSymmetry = function() {
        var from_offset = 0;
        var to_offset = 0;
        var i;
        var j = 0;
        var buffer = this.image.newBuffer;
        var bufferWidth = this.image.width;
        for (i = 0; i < this.rows.length; i++) {
            if ((this.rows[i].symTo >= 0) && (!this.rows[this.rows[i].symTo].dirty)) {
                from_offset = this.rows[i].symTo * bufferWidth;
                arrayCopy(buffer, from_offset, buffer, to_offset, bufferWidth);
                this.rows[i].dirty = false;
            }
            to_offset += bufferWidth;
        }
        for (i = 0; i < this.columns.length; i++) {
            if ((this.columns[i].symTo >= 0) && (!this.columns[this.columns[i].symTo].dirty)) {
                to_offset = i;
                from_offset = this.columns[i].symTo;
                for (j = 0; j < this.rows.length; j++) {
                    buffer[to_offset] = buffer[from_offset];
                    to_offset += bufferWidth;
                    from_offset += bufferWidth;
                }
                this.columns[i].dirty = false;
            }
        }
    }

    /** Build an optimized move table based on relocation table */
    ZoomContext.prototype.prepareMove = function() {
        var move = null;
        var i = 0;
        var j = 0;
        var s = 0;
        while (i < this.columns.length) {
            if (!this.columns[i].dirty) {
                move = this.moveTable[s];
                move.to = i;
                move.length = 1;
                move.from = this.columns[i].symIndex;
                for (j = i + 1; j < this.columns.length; j++) {
                    if (this.columns[j].dirty || ((j - this.columns[j].symIndex) !== (move.to - move.from))) {
                        break;
                    }
                    move.length++;
                }
                i = j;
                s++;
            } else {
                i++;
            }
        }
        move = this.moveTable[s];
        move.length = 0;
    }

    /** Execute moves defined in move table */
    ZoomContext.prototype.doMove = function() {
        var move = null;
        var newOffset = 0;
        var oldOffset = 0;
        var from = 0;
        var to = 0;
        var i;
        var s = 0;
        var length = 0;
        var newBuffer = this.image.newBuffer;
        var oldBuffer = this.image.oldBuffer;
        var bufferWidth = this.image.width;
        for (i = 0; i < this.rows.length; i++) {
            if (!this.rows[i].dirty) {
                s = 0;
                oldOffset = this.rows[i].symIndex * bufferWidth;
                while ((move = this.moveTable[s]).length > 0) {
                    from = oldOffset + move.from;
                    to = newOffset + move.to;
                    length = move.length;
                    arrayCopy(oldBuffer, from, newBuffer, to, length);
                    s++;
                }
            }
            newOffset += bufferWidth;
        }
    }

    /** Shortcut for prepare and execute move */
    ZoomContext.prototype.movePixels = function() {
        this.prepareMove();
        this.doMove();
    }

    /** Prepare fill table based on relocation table */
    ZoomContext.prototype.prepareFill = function() {
        var fill = null;
        var i;
        var j = 0;
        var k = 0;
        var s = 0;
        var n = 0;
        for (i = 0; i < this.columns.length; i++) {
            if (this.columns[i].dirty) {
                j = i - 1;
                for (k = i + 1; (k < this.columns.length) && this.columns[k].dirty; k++) {}
                while ((i < this.columns.length) && this.columns[i].dirty) {
                    if ((k < this.columns.length) && ((j < i) || ((this.columns[i].newPosition - this.columns[j].newPosition) > (this.columns[k].newPosition - this.columns[i].newPosition)))) {
                        j = k;
                    } else if (j < 0) {
                        break;
                    }
                    n = k - i;
                    fill = this.fillTable[s];
                    fill.length = n;
                    fill.from = j;
                    fill.to = i;
                    while (n > 0) {
                        this.columns[i].newPosition = this.columns[j].newPosition;
                        this.columns[i].dirty = false;
                        n--;
                        i++;
                    }
                    s++;
                }
            }
        }
        fill = this.fillTable[s];
        fill.length = 0;
    }

    /** Apply fill table */
    ZoomContext.prototype.doFill = function() {
        var fill = null;
        var from_offset = 0;
        var to_offset = 0;
        var from = 0;
        var to = 0;
        var i;
        var j = 0;
        var k = 0;
        var t = 0;
        var s = 0;
        var d = 0;
        var buffer = this.image.newBuffer;
        var bufferWidth = this.image.width;
        for (i = 0; i < this.rows.length; i++) {
            if (this.rows[i].dirty) {
                j = i - 1;
                for (k = i + 1; (k < this.rows.length) && this.rows[k].dirty; k++) {}
                while ((i < this.rows.length) && this.rows[i].dirty) {
                    if ((k < this.rows.length) && ((j < i) || ((this.rows[i].newPosition - this.rows[j].newPosition) > (this.rows[k].newPosition - this.rows[i].newPosition)))) {
                        j = k;
                    } else if (j < 0) {
                        break;
                    }
                    to_offset = i * bufferWidth;
                    from_offset = j * bufferWidth;
                    if (!this.rows[j].dirty) {
                        s = 0;
                        while ((fill = this.fillTable[s]).length > 0) {
                            from = from_offset + fill.from;
                            to = from_offset + fill.to;
                            for (t = 0; t < fill.length; t++) {
                                d = to + t;
                                buffer[d] = buffer[from];
                            }
                            s++;
                        }
                    }
                    arrayCopy(buffer, from_offset, buffer, to_offset, bufferWidth);
                    this.rows[i].newPosition = this.rows[j].newPosition;
                    this.rows[i].dirty = true;
                    i++;
                }
            } else {
                s = 0;
                from_offset = i * bufferWidth;
                while ((fill = this.fillTable[s]).length > 0) {
                    from = from_offset + fill.from;
                    to = from_offset + fill.to;
                    for (t = 0; t < fill.length; t++) {
                        d = to + t;
                        buffer[d] = buffer[from];
                    }
                    s++;
                }
                this.rows[i].dirty = true;
            }
        }
    }

    /** Shortcut to prepare and apply fill table */
    ZoomContext.prototype.fill = function() {
        this.prepareFill();
        this.doFill();
    }

    /** Render line using solid guessing
     *
     * @param row
     */
    ZoomContext.prototype.renderRow = function(row) {
        var buffer = this.image.newBuffer;
        var bufferWidth = this.image.width;
        var newPosition = row.newPosition;
        var r = row.index;
        var offset = r * bufferWidth;
        var i;
        var j;
        var k;
        var n;
        var distl;
        var distr;
        var distu;
        var distd;
        var offsetu;
        var offsetd;
        var offsetl;
        var offsetul;
        var offsetur;
        var offsetdl;
        var offsetdr;
        var rend = r - GUESS_RANGE;
        var length;
        var current;
        if (rend < 0) {
            rend = 0;
        }
        for (i = r - 1; (i >= rend) && this.rows[i].dirty; i--) {}
        distu = r - i;
        rend = r + GUESS_RANGE;
        if (rend >= this.rows.length) {
            rend = this.rows.length - 1;
        }
        for (j = r + 1; (j < rend) && this.rows[j].dirty; j++) {}
        distd = j - r;
        if (!USE_SOLIDGUESS || (i < 0) || (j >= this.rows.length) || this.rows[i].dirty || this.rows[j].dirty) {
            for (k = 0, length = this.columns.length; k < length; k++) {
                current = this.columns[k];
                if (!this.columns[k].dirty) {
                    buffer[offset] = this.fractal.formula(current.newPosition, newPosition);
                }
                offset++;
            }
        } else {
            distr = 0;
            distl = Number.MAX_VALUE / 2;
            offsetu = offset - (distu * bufferWidth);
            offsetd = offset + (distd * bufferWidth);
            for (k = 0, length = this.columns.length; k < length; k++) {
                current = this.columns[k];
                if (!this.columns[k].dirty) {
                    if (distr <= 0) {
                        rend = k + GUESS_RANGE;
                        if (rend >= this.columns.length) {
                            rend = this.columns.length - 1;
                        }
                        for (j = k + 1; (j < rend) && this.columns[j].dirty; j++) {
                            distr = j - k;
                        }
                        if (j >= rend) {
                            distr = Number.MAX_VALUE / 2;
                        }
                    }
                    if ((distr < (Number.MAX_VALUE / 4)) && (distl < (Number.MAX_VALUE / 4))) {
                        offsetl = offset - distl;
                        offsetul = offsetu - distl;
                        offsetdl = offsetd - distl;
                        offsetur = offsetu + distr;
                        offsetdr = offsetd + distr;
                        n = buffer[offsetl];
                        if ((n == buffer[offsetu]) && (n == buffer[offsetd]) && (n == buffer[offsetul]) && (n == buffer[offsetur]) && (n == buffer[offsetdl]) && (n == buffer[offsetdr])) {
                            buffer[offset] = n;
                        } else {
                            buffer[offset] = this.fractal.formula(current.newPosition, newPosition);
                        }
                    } else {
                        buffer[offset] = this.fractal.formula(current.newPosition, newPosition);
                    }
                    distl = 0;
                }
                offset++;
                offsetu++;
                offsetd++;
                distr--;
                distl++;
            }
        }
        row.recalculate = false;
        row.dirty = false;
    }

    /** Render column using solid guessing
     *
     * @param column
     */
    ZoomContext.prototype.renderColumn = function(column) {
        var buffer = this.image.newBuffer;
        var bufferWidth = this.image.width;
        var newPosition = column.newPosition;
        var r = column.index;
        var offset = r;
        var rend = r - GUESS_RANGE;
        var i;
        var j;
        var k;
        var n;
        var distl;
        var distr;
        var distu;
        var distd;
        var offsetl;
        var offsetr;
        var offsetu;
        var offsetlu;
        var offsetru;
        var offsetld;
        var offsetrd;
        var sumu;
        var sumd;
        var length;
        var current;
        if (rend < 0) {
            rend = 0;
        }
        for (i = r - 1; (i >= rend) && this.columns[i].dirty; i--) {}
        distl = r - i;
        rend = r + GUESS_RANGE;
        if (rend >= this.columns.length) {
            rend = this.columns.length - 1;
        }
        for (j = r + 1; (j < rend) && this.columns[j].dirty; j++) {}
        distr = j - r;
        if (!USE_SOLIDGUESS || (i < 0) || (j >= this.columns.length) || this.columns[i].dirty || this.columns[j].dirty) {
            for (k = 0, length = this.rows.length; k < length; k++) {
                current = this.rows[k];
                if (!this.rows[k].dirty) {
                    buffer[offset] = this.fractal.formula(newPosition, current.newPosition);
                }
                offset += bufferWidth;
            }
        } else {
            distd = 0;
            distu = Number.MAX_VALUE / 2;
            offsetl = offset - distl;
            offsetr = offset + distr;
            for (k = 0, length = this.rows.length; k < length; k++) {
                current = this.rows[k];
                if (!this.rows[k].dirty) {
                    if (distd <= 0) {
                        rend = k + GUESS_RANGE;
                        if (rend >= this.rows.length) {
                            rend = this.rows.length - 1;
                        }
                        for (j = k + 1; (j < rend) && this.rows[j].dirty; j++) {
                            distd = j - k;
                        }
                        if (j >= rend) {
                            distd = Number.MAX_VALUE / 2;
                        }
                    }
                    if ((distd < (Number.MAX_VALUE / 4)) && (distu < (Number.MAX_VALUE / 4))) {
                        sumu = distu * bufferWidth;
                        sumd = distd * bufferWidth;
                        offsetu = offset - sumu;
                        offsetlu = offsetl - sumu;
                        offsetru = offsetr - sumu;
                        offsetld = offsetl + sumd;
                        offsetrd = offsetr + sumd;
                        n = buffer[offsetu];
                        if ((n == buffer[offsetl]) && (n == buffer[offsetr]) && (n == buffer[offsetlu]) && (n == buffer[offsetru]) && (n == buffer[offsetld]) && (n == buffer[offsetrd])) {
                            buffer[offset] = n;
                        } else {
                            buffer[offset] = this.fractal.formula(newPosition, current.newPosition);
                        }
                    } else {
                        buffer[offset] = this.fractal.formula(newPosition, current.newPosition);
                    }
                    distu = 0;
                }
                offset += bufferWidth;
                offsetl += bufferWidth;
                offsetr += bufferWidth;
                distd--;
                distu++;
            }
        }
        column.recalculate = false;
        column.dirty = false;
    }

    /** Calculate whether we're taking too long to render the fractal to meet the idealPos FPS */
    ZoomContext.prototype.tooSlow = function() {
        var newTime = new Date().getTime(),
            minFPS = this.zooming ? this.minFPS : 10;
        return 1000 / (newTime - this.startTime + this.fudgeFactor) < minFPS;
    }

    /** Prioritize calculation of lines between begin and end
     *
     * @param lines - rows or columns to prioritize
     * @param begin - index of first line to prioritize
     * @param end - index of last line to prioritize
     */
    function calcPriority(lines, begin, end) {
        var middle;
        while (begin < end) {
            middle = begin + ((end - begin) >> 1);
            lines[middle].priority = (lines[end].newPosition - lines[middle].newPosition) * lines[middle].priority;
            if (lines[middle].symRef !== -1) {
                lines[middle].priority /= 2.0;
            }
            calcPriority(lines, begin, middle);
            begin = middle + 1;
        }
    }

    /** Enqueue all the lines to be recalculated and set their priority
     *
     * @param lines - lines to enqueue for calculation
     */
    ZoomContext.prototype.enqueueCalculations = function(lines) {
        var i;
        var j = 0;
        for (i = 0; i < lines.length; i++) {
            if (lines[i].recalculate) {
                for (j = i; (j < lines.length) && lines[j].recalculate; j++) {
                    this.queue[this.queueLength++] = lines[j];
                }
                if (j === lines.length) {
                    j -= 1;
                }
                calcPriority(lines, i, j);
                i = j;
            }
        }
    }

    /** Sort calculation queue according to priority (using quicksort)
     *
     * @param queue
     * @param l
     * @param r
     */
    function sortQueue(queue, l, r) {
        var m = (queue[l].priority + queue[r].priority) / 2.0;
        var tmp = null;
        var i = l;
        var j = r;
        do {
            while (queue[i].priority > m) {
                i++;
            }
            while (queue[j].priority < m) {
                j--;
            }
            if (i <= j) {
                tmp = queue[i];
                queue[i] = queue[j];
                queue[j] = tmp;
                i++;
                j--;
            }
        }
        while (j >= i);
        if (l < j) {
            sortQueue(queue, l, j);
        }
        if (r > i) {
            sortQueue(queue, i, r);
        }
    }

    /** Process the relocation table */
    ZoomContext.prototype.calculate = function() {
        var i, newTime;
        this.incomplete = false;
        this.queueLength = 0;
        this.enqueueCalculations(this.columns);
        this.enqueueCalculations(this.rows);
        if (this.queueLength > 0) {
            if (this.queueLength > 1) {
                sortQueue(this.queue, 0, this.queueLength - 1);
            }
            for (i = 0; i < this.queueLength; i++) {
                if (this.queue[i].isRow) {
                    this.renderRow(this.queue[i]);
                } else {
                    this.renderColumn(this.queue[i]);
                }
                if (!this.recalculate && this.tooSlow() && (i < this.queueLength)) {
                    this.incomplete = true;
                    this.fill();
                    break;
                }
            }
        }
    };

    /** Update newPosition array with newly calculated positions */
    ZoomContext.prototype.updatePosition = function() {
        var k;
        var len;
        for (k = 0,len = this.columns.length; k < len; k++) {
            this.columns[k].oldPosition = this.columns[k].newPosition;
        }
        for (k = 0,len = this.rows.length; k < len; k++) {
            this.rows[k].oldPosition = this.rows[k].newPosition;
        }
    };

    /** Calculate FPS achieved and determine if fudge factor needs adjustment for next frame */
    ZoomContext.prototype.updateFPS = function() {
        var fps = 1000 / (new Date().getTime() - this.startTime);
        if (fps < this.minFPS) {
            this.fudgeFactor++;
        } else if (fps > this.minFPS + 10 && this.fudgeFactor > 0) {
            this.fudgeFactor--;
        }
        console.log(fps + " fps");
    };

    /** Overall fractal drawing workflow, calls other functions */
    ZoomContext.prototype.drawFractal = function(recalculate) {
        var area = this.convertArea();
        var symx = this.fractal.symmetry && this.fractal.symmetry.x;
        var symy = this.fractal.symmetry && this.fractal.symmetry.y;
        var stepx, stepy;
        this.startTime = new Date().getTime();
        this.recalculate = recalculate;
        if (recalculate || !USE_XAOS) {
            stepx = this.initialize(this.columns, area.begin.x, area.end.x, false);
            stepy = this.initialize(this.rows, area.begin.y, area.end.y, true);
        } else {
            stepx = this.approximate(this.columns, area.begin.x, area.end.x);
            stepy = this.approximate(this.rows, area.begin.y, area.end.y);
        }
        if (USE_SYMMETRY && typeof symy === "number" && !(area.begin.y > symy || symy > area.end.y)) {
            prepareSymmetry(this.rows, Math.floor((symy - area.begin.y) / stepy), symy, stepy);
        }
        if (USE_SYMMETRY && typeof symx === "number" && !(area.begin.x > symx || symx > area.end.x)) {
            prepareSymmetry(this.columns, Math.floor((symx - area.begin.x) / stepx), symx, stepx);
        }
        this.image.swapBuffers();
        this.movePixels();
        this.calculate();
        if (USE_SYMMETRY && typeof symx === "number" || typeof symy === "number") {
            this.doSymmetry();
        }
        this.image.paint();
        this.updatePosition();
        this.updateFPS();
    };

    /** Adjust display region to zoom based on mouse buttons */
    ZoomContext.prototype.updateRegion = function(mouse) {
        var MAXSTEP = 0.008 * 3;
        var MUL = 0.3;
        var area = this.convertArea();
        var x = area.begin.x + mouse.x * ((area.end.x - area.begin.x) / this.image.width);
        var y = area.begin.y + mouse.y * ((area.end.y - area.begin.y) / this.image.height);
        var deltax = (mouse.oldx - mouse.x) * ((area.end.x - area.begin.x) / this.image.width);
        var deltay = (mouse.oldy - mouse.y) * ((area.end.y - area.begin.y) / this.image.height);
        var step;
        var mmul;
        if (mouse.button[1] || (mouse.button[0] && mouse.button[2])) {
            // Pan when middle or left+right buttons are pressed
            step = 0;
        } else if (mouse.button[0]) {
            // Zoom in when left button is pressed
            step = MAXSTEP * 2;
        } else if (mouse.button[2]) {
            // Zoom out when right button is pressed
            step = -MAXSTEP * 2;
        } else {
            this.zooming = false;
            return;
        }
        mmul = Math.pow((1 - step), MUL);
        area.begin.x = x + (area.begin.x - x) * mmul;
        area.end.x = x + (area.end.x - x) * mmul;
        area.begin.y = y + (area.begin.y - y) * mmul;
        area.end.y = y + (area.end.y - y) * mmul;
        this.fractal.region.radius.x = area.end.x - area.begin.x;
        this.fractal.region.radius.y = area.end.y - area.begin.y;
        this.fractal.region.center.x = (area.begin.x + area.end.x) / 2;
        this.fractal.region.center.y = ((area.begin.y + area.end.y) / 2) * (this.image.width / this.image.height);
        this.zooming = true;
    };

    /** Attaches zoomer to specified canvas */
    return function(canvas, fractal) {
        var image = new CanvasImage(canvas);
        var zoomer = new ZoomContext(image, fractal);
        var mouse = { x: 0, y: 0, button: [false, false, false] };

        function doZoom() {
            zoomer.updateRegion(mouse);
            if (zoomer.zooming || zoomer.incomplete) {
                requestAnimationFrame(doZoom);
                zoomer.drawFractal(false);
            }
        }

        canvas.ontouchstart = function(e) {
            if(e.touches.length < 3){
                var touch = e.touches[0];
                (e.touches.length == 2)?mouse.button[2]=true:mouse.button[2]=false;
                var mouseEvent = new MouseEvent("mousedown", {
                    clientX: touch.clientX,
                    clientY: touch.clientY
                });
                canvas.dispatchEvent(mouseEvent);
            }
        };

        canvas.ontouchend = function(e) {
            var mouseEvent = new MouseEvent("mouseup", {});
            canvas.dispatchEvent(mouseEvent);
        };

        canvas.ontouchmove = function(e) {
            var touch = e.touches[0];
            var mouseEvent = new MouseEvent("mousemove", {
                clientX: touch.clientX,
                clientY: touch.clientY
            });
            canvas.dispatchEvent(mouseEvent);
        };

        canvas.onmousedown =  function(e) {
            mouse.button[e.button] = true;
            mouse.x = e.offsetX || (e.clientX - canvas.offsetLeft);
            mouse.y = e.offsetY || (e.clientY - canvas.offsetTop);
            mouse.oldx = e.offsetX || (e.clientX - canvas.offsetLeft);
            mouse.oldy = e.offsetY || (e.clientY - canvas.offsetTop);
            doZoom();
        };

        canvas.onmouseup = function(e) {
            mouse.button[e.button] = false;
        };

        canvas.onmousemove = function(e) {
            mouse.x = e.offsetX || (e.clientX - canvas.offsetLeft);
            mouse.y = e.offsetY || (e.clientY - canvas.offsetTop);
        };

        canvas.oncontextmenu = function() {
            return false;
        };

        canvas.onmouseout = function() {
            mouse.button = [false, false, false];
        };

        zoomer.drawFractal(true);
    }
}());

/** Create the default XaoS color palette */
xaos.defaultPalette = function() {
    var MAXENTRIES = 65536;
    var segmentsize = 8;
    var setsegments = Math.floor((MAXENTRIES + 3) / segmentsize);
    var nsegments = Math.floor(255 / segmentsize);
    var segments = [
        [0, 0, 0],
        [120, 119, 238],
        [24, 7, 25],
        [197, 66, 28],
        [29, 18, 11],
        [135, 46, 71],
        [24, 27, 13],
        [241, 230, 128],
        [17, 31, 24],
        [240, 162, 139],
        [11, 4, 30],
        [106, 87, 189],
        [29, 21, 14],
        [12, 140, 118],
        [10, 6, 29],
        [50, 144, 77],
        [22, 0, 24],
        [148, 188, 243],
        [4, 32, 7],
        [231, 146, 14],
        [10, 13, 20],
        [184, 147, 68],
        [13, 28, 3],
        [169, 248, 152],
        [4, 0, 34],
        [62, 83, 48],
        [7, 21, 22],
        [152, 97, 184],
        [8, 3, 12],
        [247, 92, 235],
        [31, 32, 16]
    ];
    var i, y;
    var r, g, b;
    var rs, gs, bs;
    var palette = [];

    for (i = 0; i < setsegments; i++) {
        r = segments[i % nsegments][0];
        g = segments[i % nsegments][1];
        b = segments[i % nsegments][2];
        rs = (segments[(i + 1) % setsegments % nsegments][0] - r) / segmentsize;
        gs = (segments[(i + 1) % setsegments % nsegments][1] - g) / segmentsize;
        bs = (segments[(i + 1) % setsegments % nsegments][2] - b) / segmentsize;
        for (y = 0; y < segmentsize; y++) {
            palette.push(255<<24 | b << 16 | g << 8 | r);
            r += rs;
            g += gs;
            b += bs;
        }
    }
    return new Uint32Array(palette);
};

xaos.mandelbrot = {
    symmetry: {x: null, y: 0 },
    region: {
        center: { x: -0.75, y: 0.0 },
        radius: { x: 2.5, y : 2.5 },
        angle: 0
    },
    z0: { x: 0, y: 0 },
    maxiter: 512,
    bailout: 4,
    formula: function(cr, ci) {
        var maxiter = this.maxiter,
            bailout = this.bailout,
            zr = this.z0.x,
            zi = this.z0.y,
            i = maxiter;

        while (i--) {
            var zr2 = zr * zr;
            var zi2 = zi * zi;

            if (zr2 + zi2 > bailout) {
                return this.palette[(maxiter - i) % this.palette.length];
            }

            zi = ci + (2 * zr * zi);
            zr = cr + zr2 - zi2;
        }

        return this.palette[0];
    },
    palette: xaos.defaultPalette()
};

xaos.zoom(document.getElementById("canvas"), xaos.mandelbrot);