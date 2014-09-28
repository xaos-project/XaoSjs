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

xaos.zoom = function(canvas, fractal) {
    "use strict";
    var MODE_CALCULATE = 0x01,
        USE_XAOS = true,
        USE_SYMMETRY = true,
        USE_SOLIDGUESS = true,
        RANGES = 2,
        RANGE = 4,
        MASK = 0x7,
        DSIZE = (RANGES + 1),
        FPMUL = 64,
        FPRANGE = FPMUL * RANGE,
        MAX_PRICE = Number.MAX_VALUE,
        NEW_PRICE = FPRANGE * FPRANGE,
        GUESS_RANGE = 4,
        mouse = { x: 0, y: 0, button: [false, false, false] },
        bufferWidth = canvas.width,
        renderMode = MODE_CALCULATE;

    var area = convertArea();
    var isVerticalSymmetrySupported = (USE_SYMMETRY && fractal.symmetry && typeof fractal.symmetry.y === "number") || false;
    var isHorizontalSymmetrySupported = (USE_SYMMETRY && fractal.symmetry && typeof fractal.symmetry.x === "number") || false;

    /** Utility function to pre-allocate an array of the specified size
     * with the specified initial value. It will do the right thing
     * to create unique items, whether you pass in a prototype, a
     * constructor, or a primitive.
     * @param {number} size - the size of the array.
     * @param initial - the initial value for each entry.
     */
    function preAllocArray(size, initial) {
        var i, data = [];
        for (i = 0; i < size; i += 1) {
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

    /** Creates a single entry for a move or fill table.
     * @constructor
     */
    function TableEntry() {
        this.length = 0;
        this.from = 0;
        this.to = 0;
    }

    /** Creates a single entry for a dynamic data table.
     * @constructor
     */
    function DynamicEntry() {
        this.previous = null;
        this.pos = 0;
        this.price = 0;
    }

    /** Creates a single entry for a reallocation table.
     * @constructor
     */
    function ReallocEntry() {
        this.recalculate = false;
        this.dirty = false;
        this.line = false;
        this.pos = 0;
        this.plus = 0;
        this.symTo = 0;
        this.symRef = 0;
        this.position = 0.0;
        this.priority = 0.0;
    }

    /** Container for dynamic algorithm data.
     * @param {number} size - the number of entries to allocate.
     * @constructor
     */
    function DynamicContainer(size) {
        this.delta = preAllocArray(size + 1, 0);
        this.oldBest = preAllocArray(size, DynamicEntry);
        this.newBest = preAllocArray(size, DynamicEntry);
        this.calData = preAllocArray(size, DynamicEntry);
        this.conData = preAllocArray(size << DSIZE, DynamicEntry);
    }


    /** Swaps the old and new best prices in the dynamic container. */
    DynamicContainer.prototype.swap = function() {
        var tmpBest = this.oldBest;
        this.oldBest = this.newBest;
        this.newBest = tmpBest;
    };

    /** Container for all zoom context data for a particular canvas.
     *
     * @param canvas {Canvas} HTML5 canvas on which to draw the fractal.
     * @constructor
     */
    function ZoomContext(canvas) {
        this.context = canvas.getContext("2d");
        this.newImage = this.context.createImageData(canvas.width, canvas.height);
        this.newBuffer = new Uint32Array(this.newImage.data.buffer);
        this.oldImage = this.context.createImageData(canvas.width, canvas.height);
        this.oldBuffer = new Uint32Array(this.oldImage.data.buffer);
        this.positionX = preAllocArray(canvas.width, 0.0);
        this.positionY = preAllocArray(canvas.height, 0.0);
        this.reallocX = preAllocArray(canvas.width, ReallocEntry);
        this.reallocY = preAllocArray(canvas.height, ReallocEntry);
        this.dynamicX = new DynamicContainer(canvas.width);
        this.dynamicY = new DynamicContainer(canvas.height);
        this.moveTable = preAllocArray(canvas.width + 1, TableEntry);
        this.fillTable = preAllocArray(canvas.width + 1, TableEntry);
        this.queue = preAllocArray(canvas.width + canvas.height, ReallocEntry);
        this.startTime = 0;
        this.fudgeFactor = 0;
        this.incomplete = false;
    }

    var renderedData = new ZoomContext(canvas);

    /** Optimized array copy using Duff's Device.
     *
     * @param from {Array} source array
     * @param fromOffset {number} offset into source array
     * @param to {Array} target array
     * @param toOffset {number} offset into target array
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

    /** Convert fractal viewport from radius/center to x start-end and y start-end */
    function convertArea() {
        var radius = fractal.region.radius;
        var center = fractal.region.center;
        var aspect = canvas.width / canvas.height;
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
    }

    /** Calculate the best approximation for points based on previous frame
     *
     * @param realloc - reallocation table for rows or columns
     * @param dynamic - temporary data for dynamic algorithm
     * @param begin - beginning coordinate (x or y)
     * @param end - ending coordinate (x or y)
     * @param position - array of position coordinates on the complex plane
     * @returns {number}
     */
    function makeReallocTable (realloc, dynamic, begin, end, position) {
        var tmpRealloc = null;
        var prevData = null;
        var bestData = null;
        var bestPrice = MAX_PRICE;
        var price = 0;
        var price1 = 0;
        var i;
        var y = 0;
        var p = 0;
        var ps = 0;
        var pe = 0;
        var ps1 = 0;
        var yend = 0;
        var flag = 0;
        var size = realloc.length;
        var step = (end - begin) / size;
        var tofix = (size * FPMUL) / (end - begin);
        var delta = dynamic.delta;

        delta[size] = Number.MAX_VALUE;
        for (i = size - 1; i >= 0; i--) {
            delta[i] = ((position[i] - begin) * tofix)|0;
            if (delta[i] > delta[i + 1]) {
                delta[i] = delta[i + 1];
            }
        }

        for (i = 0; i < size; i++) {
            dynamic.swap();
            yend = y - FPRANGE;
            if (yend < 0) {
                yend = 0;
            }
            p = ps;
            while (delta[p] < yend) {
                p += 1;
            }
            ps1 = p;
            yend = y + FPRANGE;
            if ((ps !== pe) && (p > ps)) {
                if (p < pe) {
                    prevData = dynamic.oldBest[p - 1];
                } else {
                    prevData = dynamic.oldBest[pe - 1];
                }
                price1 = prevData.price;
            } else if (i > 0) {
                prevData = dynamic.calData[i - 1];
                price1 = prevData.price;
            } else {
                prevData = null;
                price1 = 0;
            }

            price = price1 + NEW_PRICE;
            bestData = dynamic.calData[i];
            bestPrice = price;
            bestData.price = price;
            bestData.pos = -1;
            bestData.previous = prevData;

            if (ps !== pe) {
                if (p === ps) {
                    if (delta[p] !== delta[p + 1]) {
                        prevData = dynamic.calData[i - 1];
                        price1 = prevData.price;
                        price = price1 + calcPrice(delta[p], y);
                        if (price < bestPrice) {
                            bestData = dynamic.conData[(p << DSIZE) + (i & MASK)];
                            bestPrice = price;
                            bestData.price = price;
                            bestData.pos = p;
                            bestData.previous = prevData;
                        }
                    }
                    dynamic.newBest[p++] = bestData;
                }
                prevData = null;
                price1 = price;
                while (p < pe) {
                    if (delta[p] !== delta[p + 1]) {
                        prevData = dynamic.oldBest[p - 1];
                        price1 = prevData.price;
                        price = price1 + NEW_PRICE;
                        if (price < bestPrice) {
                            bestData = dynamic.conData[((p - 1) << DSIZE) + (i & MASK)];
                            bestPrice = price;
                            bestData.price = price;
                            bestData.pos = -1;
                            bestData.previous = prevData;
                            dynamic.newBest[p - 1] = bestData;
                        }
                        price = price1 + calcPrice(delta[p], y);
                        if (price < bestPrice) {
                            bestData = dynamic.conData[(p << DSIZE) + (i & MASK)];
                            bestPrice = price;
                            bestData.price = price;
                            bestData.pos = p;
                            bestData.previous = prevData;
                        } else if (delta[p] > y) {
                            dynamic.newBest[p++] = bestData;
                            break;
                        }
                    }
                    dynamic.newBest[p++] = bestData;
                }
                if (p > ps) {
                    prevData = dynamic.oldBest[p - 1];
                    price1 = prevData.price;
                } else {
                    prevData = dynamic.calData[i - 1];
                    price1 = prevData.price;
                }
                price = price1 + NEW_PRICE;
                if ((price < bestPrice) && (p > ps1)) {
                    bestData = dynamic.conData[((p - 1) << DSIZE) + (i & MASK)];
                    bestPrice = price;
                    bestData.price = price;
                    bestData.pos = -1;
                    bestData.previous = prevData;
                    dynamic.newBest[p - 1] = bestData;
                }
                while (delta[p] < yend) {
                    if (delta[p] !== delta[p + 1]) {
                        price = price1 + calcPrice(delta[p], y);
                        if (price < bestPrice) {
                            bestData = dynamic.conData[(p << DSIZE) + (i & MASK)];
                            bestPrice = price;
                            bestData.price = price;
                            bestData.pos = p;
                            bestData.previous = prevData;
                        } else if (delta[p] > y) {
                            break;
                        }
                    }
                    dynamic.newBest[p++] = bestData;
                }
                while (delta[p] < yend) {
                    dynamic.newBest[p++] = bestData;
                }
            } else if (delta[p] < yend) {
                if (i > 0) {
                    prevData = dynamic.calData[i - 1];
                    price1 = prevData.price;
                } else {
                    prevData = null;
                    price1 = 0;
                }
                while (delta[p] < yend) {
                    if (delta[p] !== delta[p + 1]) {
                        price = price1 + calcPrice(delta[p], y);
                        if (price < bestPrice) {
                            bestData = dynamic.conData[(p << DSIZE) + (i & MASK)];
                            bestPrice = price;
                            bestData.price = price;
                            bestData.pos = p;
                            bestData.previous = prevData;
                        } else if (delta[p] > y) {
                            break;
                        }
                    }
                    dynamic.newBest[p++] = bestData;
                }
                while (delta[p] < yend) {
                    dynamic.newBest[p++] = bestData;
                }

            }
            ps = ps1;
            ps1 = pe;
            pe = p;
            y += FPMUL;
        }
        if ((begin > delta[0]) && (end < delta[size - 1])) {
            flag = 1;
        }
        if ((delta[0] > 0) && (delta[size - 1] < (size * FPMUL))) {
            flag = 2;
        }
        for (i = size - 1; i >= 0; i--) {
            tmpRealloc = realloc[i];
            tmpRealloc.symTo = -1;
            tmpRealloc.symRef = -1;
            if (bestData.pos < 0) {
                tmpRealloc.recalculate = true;
                tmpRealloc.dirty = true;
                tmpRealloc.plus = tmpRealloc.pos;
            } else {
                tmpRealloc.plus = bestData.pos;
                tmpRealloc.position = position[bestData.pos];
                tmpRealloc.recalculate = false;
                tmpRealloc.dirty = false;
            }
            bestData = bestData.previous;
        }
        newPositions(realloc, size, begin, end, step, position, flag);
        return step;
    }

    /** Resets reallocation table for fresh calculation
     *
     * @param realloc - reallocation table
     * @param position - array of coordinates for line or column in the complex plane
     * @param begin - starting cooridnate
     * @param end - ending coordinate
     * @param line - whether this is a line or column
     * @returns {number}
     */
    function initReallocTableAndPosition(realloc, position, begin, end, line) {
        var i, p, step = (end - begin) / realloc.length;
        for (i = 0, p = begin; i < realloc.length; i++, p += step) {
            position[i] = p;
            realloc[i].recalculate = true;
            realloc[i].dirty = true;
            realloc[i].line = line;
            realloc[i].pos = i;
            realloc[i].position = p;
            realloc[i].plus = i;
            realloc[i].symTo = -1;
            realloc[i].symRef = -1;
        }
        return step;
    }

    /** Calculate new positions based on reallocation table
     *
     * @param realloc
     * @param size
     * @param begin1
     * @param end1
     * @param step
     * @param position
     * @param flag
     */
    function newPositions(realloc, size, begin1, end1, step, position, flag) {
        var tmpRealloc = null;
        var delta = 0;
        var begin = 0;
        var end = 0;
        var s = -1;
        var e = -1;
        if (begin1 > end1) {
            begin1 = end1;
        }
        while (s < (size - 1)) {
            e = s + 1;
            if (realloc[e].recalculate) {
                while (e < size) {
                    if (!realloc[e].recalculate) {
                        break;
                    }
                    e++;
                }
                if (e < size) {
                    end = realloc[e].position;
                } else {
                    end = end1;
                }
                if (s < 0) {
                    begin = begin1;
                } else {
                    begin = realloc[s].position;
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
                            tmpRealloc = realloc[s];
                            tmpRealloc.position = begin;
                            tmpRealloc.priority = 1 / (1 + (Math.abs((position[s] - begin)) * step));
                        }
                        break;
                    case 2:
                        for (s++; s < e; s++) {
                            begin += delta;
                            tmpRealloc = realloc[s];
                            tmpRealloc.position = begin;
                            tmpRealloc.priority = Math.abs((position[s] - begin)) * step;
                        }
                        break;
                    default:
                        for (s++; s < e; s++) {
                            begin += delta;
                            tmpRealloc = realloc[s];
                            tmpRealloc.position = begin;
                            tmpRealloc.priority = 1.0;
                        }
                        break;
                }
            }
            s = e;
        }
    }

    /** Populate symmetry data into reallocation table
     *
     * @param realloc
     * @param symi
     * @param symPosition
     * @param step
     */
    function prepareSymmetry(realloc, symi, symPosition, step) {
        var i;
        var j = 0;
        var tmp;
        var abs;
        var distance;
        var tmpPosition;
        var size = realloc.length;
        var max = size - RANGE - 1;
        var min = RANGE;
        var istart = 0;
        var tmpRealloc = null;
        var symRealloc = null;
        var symj = (2 * symi) - size;
        symPosition *= 2;
        if (symj < 0) {
            symj = 0;
        }
        distance = step * RANGE;
        for (i = symj; i < symi; i++) {
            if (realloc[i].symTo !== -1) {
                continue;
            }
            tmpRealloc = realloc[i];
            tmpPosition = tmpRealloc.position;
            tmpRealloc.symTo = (2 * symi) - i;
            if (tmpRealloc.symTo > max) {
                tmpRealloc.symTo = max;
            }
            j = ((tmpRealloc.symTo - istart) > RANGE) ? (-RANGE) : (-tmpRealloc.symTo + istart);
            if (tmpRealloc.recalculate) {
                while ((j < RANGE) && ((tmpRealloc.symTo + j) < (size - 1))) {
                    tmp = symPosition - realloc[tmpRealloc.symTo + j].position;
                    abs = Math.abs(tmp - tmpPosition);
                    if (abs < distance) {
                        if (((i === 0) || (tmp > realloc[i - 1].position)) && (tmp < realloc[i + 1].position)) {
                            distance = abs;
                            min = j;
                        }
                    } else if (tmp < tmpPosition) {
                        break;
                    }
                    j += 1;
                }
            } else {
                while ((j < RANGE) && ((tmpRealloc.symTo + j) < (size - 1))) {
                    if (tmpRealloc.recalculate) {
                        tmp = symPosition - realloc[tmpRealloc.symTo + j].position;
                        abs = Math.abs(tmp - tmpPosition);
                        if (abs < distance) {
                            if (((i === 0) || (tmp > realloc[i - 1].position)) && (tmp < realloc[i + 1].position)) {
                                distance = abs;
                                min = j;
                            }
                        } else if (tmp < tmpPosition) {
                            break;
                        }
                    }
                    j += 1;
                }
            }
            tmpRealloc.symTo += min;
            symRealloc = realloc[tmpRealloc.symTo];
            if ((min === RANGE) || (tmpRealloc.symTo <= symi) || (symRealloc.symTo !== -1) || (symRealloc.symRef !== -1)) {
                tmpRealloc.symTo = -1;
                continue;
            }
            if (!tmpRealloc.recalculate) {
                tmpRealloc.symTo = -1;
                if ((symRealloc.symTo !== -1) || !symRealloc.recalculate) {
                    continue;
                }
                symRealloc.plus = tmpRealloc.plus;
                symRealloc.symTo = i;
                istart = tmpRealloc.symTo - 1;
                symRealloc.recalculate = false;
                symRealloc.dirty = true;
                tmpRealloc.symRef = tmpRealloc.symTo;
                symRealloc.position = symPosition - tmpRealloc.position;
            } else {
                if (symRealloc.symTo !== -1) {
                    tmpRealloc.symTo = -1;
                    continue;
                }
                tmpRealloc.plus = symRealloc.plus;
                istart = tmpRealloc.symTo - 1;
                tmpRealloc.recalculate = false;
                tmpRealloc.dirty = true;
                symRealloc.symRef = i;
                tmpRealloc.position = symPosition - symRealloc.position;
            }
        }
    }

    /** Apply previously calculated symmetry to image
     *
     * @param reallocX
     * @param reallocY
     */
    function doSymmetry(reallocX, reallocY) {
        var from_offset = 0;
        var to_offset = 0;
        var i;
        var j = 0;
        var newRGB = renderedData.newBuffer;
        for (i = 0; i < reallocY.length; i++) {
            if ((reallocY[i].symTo >= 0) && (!reallocY[reallocY[i].symTo].dirty)) {
                from_offset = reallocY[i].symTo * bufferWidth;
                arrayCopy(newRGB, from_offset, newRGB, to_offset, bufferWidth);
                reallocY[i].dirty = false;
            }
            to_offset += bufferWidth;
        }
        for (i = 0; i < reallocX.length; i++) {
            if ((reallocX[i].symTo >= 0) && (!reallocX[reallocX[i].symTo].dirty)) {
                to_offset = i;
                from_offset = reallocX[i].symTo;
                for (j = 0; j < reallocY.length; j++) {
                    newRGB[to_offset] = newRGB[from_offset];
                    to_offset += bufferWidth;
                    from_offset += bufferWidth;
                }
                reallocX[i].dirty = false;
            }
        }
    }

    /** Build an optimized move table based on reallocation table
     *
     * @param movetable
     * @param reallocX
     */
    function prepareMove(movetable, reallocX) {
        var tmpData = null;
        var i = 0;
        var j = 0;
        var s = 0;
        while (i < reallocX.length) {
            if (!reallocX[i].dirty) {
                tmpData = movetable[s];
                tmpData.to = i;
                tmpData.length = 1;
                tmpData.from = reallocX[i].plus;
                for (j = i + 1; j < reallocX.length; j++) {
                    if (reallocX[j].dirty || ((j - reallocX[j].plus) !== (tmpData.to - tmpData.from))) {
                        break;
                    }
                    tmpData.length += 1;
                }
                i = j;
                s += 1;
            } else {
                i += 1;
            }
        }
        tmpData = movetable[s];
        tmpData.length = 0;
    }

    /** Execute moves defined in movetable
     *
     * @param movetable
     * @param reallocY
     */
    function doMove(movetable, reallocY) {
        var tmpData = null;
        var new_offset = 0;
        var old_offset = 0;
        var from = 0;
        var to = 0;
        var i;
        var s = 0;
        var length = 0;
        var newData = renderedData.newBuffer;
        var oldData = renderedData.oldBuffer;
        for (i = 0; i < reallocY.length; i++) {
            if (!reallocY[i].dirty) {
                s = 0;
                old_offset = reallocY[i].plus * bufferWidth;
                while ((tmpData = movetable[s]).length > 0) {
                    from = old_offset + tmpData.from;
                    to = new_offset + tmpData.to;
                    length = tmpData.length;
                    arrayCopy(oldData, from, newData, to, length);
                    s += 1;
                }
            }
            new_offset += bufferWidth;
        }
    }

    /** Shortcut for prepare and execute move */
    function move() {
        prepareMove(renderedData.moveTable, renderedData.reallocX);
        doMove(renderedData.moveTable, renderedData.reallocY);
    }

    /** Prepare filltable based on reallocation table
     *
     * @param filltable
     * @param reallocX
     */
    function prepareFill(filltable, reallocX) {
        var tmpData = null;
        var i;
        var j = 0;
        var k = 0;
        var s = 0;
        var n = 0;
        for (i = 0; i < reallocX.length; i++) {
            if (reallocX[i].dirty) {
                j = i - 1;
                for (k = i + 1; (k < reallocX.length) && reallocX[k].dirty; k++) {}
                while ((i < reallocX.length) && reallocX[i].dirty) {
                    if ((k < reallocX.length) && ((j < i) || ((reallocX[i].position - reallocX[j].position) > (reallocX[k].position - reallocX[i].position)))) {
                        j = k;
                    } else if (j < 0) {
                        break;
                    }
                    n = k - i;
                    tmpData = filltable[s];
                    tmpData.length = n;
                    tmpData.from = j;
                    tmpData.to = i;
                    while (n > 0) {
                        reallocX[i].position = reallocX[j].position;
                        reallocX[i].dirty = false;
                        n -= 1;
                        i += 1;
                    }
                    s += 1;
                }
            }
        }
        tmpData = filltable[s];
        tmpData.length = 0;
    }

    /** Apply fill table
     *
     * @param filltable
     * @param reallocY
     */
    function doFill(filltable, reallocY) {
        var tmpData = null;
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
        var newRGB = renderedData.newBuffer;
        for (i = 0; i < reallocY.length; i++) {
            if (reallocY[i].dirty) {
                j = i - 1;
                for (k = i + 1; (k < reallocY.length) && reallocY[k].dirty; k++) {}
                while ((i < reallocY.length) && reallocY[i].dirty) {
                    if ((k < reallocY.length) && ((j < i) || ((reallocY[i].position - reallocY[j].position) > (reallocY[k].position - reallocY[i].position)))) {
                        j = k;
                    } else if (j < 0) {
                        break;
                    }
                    to_offset = i * bufferWidth;
                    from_offset = j * bufferWidth;
                    if (!reallocY[j].dirty) {
                        s = 0;
                        while ((tmpData = filltable[s]).length > 0) {
                            from = from_offset + tmpData.from;
                            to = from_offset + tmpData.to;
                            for (t = 0; t < tmpData.length; t++) {
                                d = to + t;
                                newRGB[d] = newRGB[from];
                            }
                            s += 1;
                        }
                    }
                    arrayCopy(renderedData.newBuffer, from_offset, renderedData.newBuffer, to_offset, bufferWidth);
                    reallocY[i].position = reallocY[j].position;
                    reallocY[i].dirty = true;
                    i += 1;
                }
            } else {
                s = 0;
                from_offset = i * bufferWidth;
                while ((tmpData = filltable[s]).length > 0) {
                    from = from_offset + tmpData.from;
                    to = from_offset + tmpData.to;
                    for (t = 0; t < tmpData.length; t++) {
                        d = to + t;
                        newRGB[d] = newRGB[from];
                    }
                    s += 1;
                }
                reallocY[i].dirty = true;
            }
        }
    }

    /** Shortcut to prepare and apply filltable */
    function fill() {
        prepareFill(renderedData.fillTable, renderedData.reallocX);
        doFill(renderedData.fillTable, renderedData.reallocY);
    }

    /** Copy pixels to screen */
    function copy() {
        renderedData.context.putImageData(renderedData.newImage, 0, 0);
    }

    /** Calculate price of approximation
     *
     * @param p1
     * @param p2
     * @returns {number}
     */
    function calcPrice(p1, p2) {
        return (p1 - p2) * (p1 - p2);
    }

    /** Add prices together to determine priority
     *
     * @param realloc
     * @param r1
     * @param r2
     */
    function addPrices(realloc, r1, r2) {
        var r3;
        while (r1 < r2) {
            r3 = r1 + ((r2 - r1) >> 1);
            realloc[r3].priority = (realloc[r2].position - realloc[r3].position) * realloc[r3].priority;
            if (realloc[r3].symRef !== -1) {
                realloc[r3].priority /= 2.0;
            }
            addPrices(realloc, r1, r3);
            r1 = r3 + 1;
        }
    }

    /** Initialize prices from reallocation table
     *
     * @param queue
     * @param total
     * @param realloc
     * @returns {*}
     */
    function initPrices(queue, total, realloc) {
        var i;
        var j = 0;
        for (i = 0; i < realloc.length; i++) {
            if (realloc[i].recalculate) {
                for (j = i; (j < realloc.length) && realloc[j].recalculate; j++) {
                    queue[total++] = realloc[j];
                }
                if (j === realloc.length) {
                    j -= 1;
                }
                addPrices(realloc, i, j);
                i = j;
            }
        }
        return total;
    }

    /** Standard quicksort alogrithm to sort queue according to priority
     *
     * @param queue
     * @param l
     * @param r
     */
    function sortQueue(queue, l, r) {
        var m = (queue[l].priority + queue[r].priority) / 2.0;
        var t = null;
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
                t = queue[i];
                queue[i] = queue[j];
                queue[j] = t;
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

    /** Render line using solid guessing
     *
     * @param realloc
     * @param reallocX
     * @param reallocY
     */
    function renderLine(realloc, reallocX, reallocY) {
        var position = realloc.position;
        var r = realloc.pos;
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
        var newRGB = renderedData.newBuffer;
        var length;
        var current;
        if (rend < 0) {
            rend = 0;
        }
        for (i = r - 1; (i >= rend) && reallocY[i].dirty; i--) {}
        distu = r - i;
        rend = r + GUESS_RANGE;
        if (rend >= reallocY.length) {
            rend = reallocY.length - 1;
        }
        for (j = r + 1; (j < rend) && reallocY[j].dirty; j++) {}
        distd = j - r;
        if (!USE_SOLIDGUESS || (i < 0) || (j >= reallocY.length) || reallocY[i].dirty || reallocY[j].dirty) {
            for (k = 0, length = reallocX.length; k < length; k++) {
                current = reallocX[k];
                if (!reallocX[k].dirty) {
                    newRGB[offset] = fractal.formula(current.position, position);
                }
                offset += 1;
            }
        } else {
            distr = 0;
            distl = Number.MAX_VALUE / 2;
            offsetu = offset - (distu * bufferWidth);
            offsetd = offset + (distd * bufferWidth);
            for (k = 0, length = reallocX.length; k < length; k++) {
                current = reallocX[k];
                if (!reallocX[k].dirty) {
                    if (distr <= 0) {
                        rend = k + GUESS_RANGE;
                        if (rend >= reallocX.length) {
                            rend = reallocX.length - 1;
                        }
                        for (j = k + 1; (j < rend) && reallocX[j].dirty; j++) {
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
                        n = newRGB[offsetl];
                        if ((n == newRGB[offsetu]) && (n == newRGB[offsetd]) && (n == newRGB[offsetul]) && (n == newRGB[offsetur]) && (n == newRGB[offsetdl]) && (n == newRGB[offsetdr])) {
                            newRGB[offset] = n;
                        } else {
                            newRGB[offset] = fractal.formula(current.position, position);
                        }
                    } else {
                        newRGB[offset] = fractal.formula(current.position, position);
                    }
                    distl = 0;
                }
                offset += 1;
                offsetu += 1;
                offsetd += 1;
                distr -= 1;
                distl += 1;
            }
        }
        realloc.recalculate = false;
        realloc.dirty = false;
    }

    /** Render column using solid guessing
     *
     * @param realloc
     * @param reallocX
     * @param reallocY
     */
    function renderColumn(realloc, reallocX, reallocY) {
        var position = realloc.position;
        var r = realloc.pos;
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
        var newRGB = renderedData.newBuffer;
        var length;
        var current;
        if (rend < 0) {
            rend = 0;
        }
        for (i = r - 1; (i >= rend) && reallocX[i].dirty; i--) {}
        distl = r - i;
        rend = r + GUESS_RANGE;
        if (rend >= reallocX.length) {
            rend = reallocX.length - 1;
        }
        for (j = r + 1; (j < rend) && reallocX[j].dirty; j++) {}
        distr = j - r;
        if (!USE_SOLIDGUESS || (i < 0) || (j >= reallocX.length) || reallocX[i].dirty || reallocX[j].dirty) {
            for (k = 0, length = reallocY.length; k < length; k++) {
                current = reallocY[k];
                if (!reallocY[k].dirty) {
                    newRGB[offset] = fractal.formula(position, current.position);
                }
                offset += bufferWidth;
            }
        } else {
            distd = 0;
            distu = Number.MAX_VALUE / 2;
            offsetl = offset - distl;
            offsetr = offset + distr;
            for (k = 0, length = reallocY.length; k < length; k++) {
                current = reallocY[k];
                if (!reallocY[k].dirty) {
                    if (distd <= 0) {
                        rend = k + GUESS_RANGE;
                        if (rend >= reallocY.length) {
                            rend = reallocY.length - 1;
                        }
                        for (j = k + 1; (j < rend) && reallocY[j].dirty; j++) {
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
                        n = newRGB[offsetu];
                        if ((n == newRGB[offsetl]) && (n == newRGB[offsetr]) && (n == newRGB[offsetlu]) && (n == newRGB[offsetru]) && (n == newRGB[offsetld]) && (n == newRGB[offsetrd])) {
                            newRGB[offset] = n;
                        } else {
                            newRGB[offset] = fractal.formula(position, current.position);
                        }
                    } else {
                        newRGB[offset] = fractal.formula(position, current.position);
                    }
                    distu = 0;
                }
                offset += bufferWidth;
                offsetl += bufferWidth;
                offsetr += bufferWidth;
                distd -= 1;
                distu += 1;
            }
        }
        realloc.recalculate = false;
        realloc.dirty = false;
    }

    function processQueue(size) {
        var i,
            newTime;
        for (i = 0; i < size; i++) {
            if (renderedData.queue[i].line) {
                renderLine(renderedData.queue[i], renderedData.reallocX, renderedData.reallocY);
            } else {
                renderColumn(renderedData.queue[i], renderedData.reallocX, renderedData.reallocY);
            }
            newTime = new Date().getTime();
            if ((renderMode & MODE_CALCULATE) === 0 && (1000 / (newTime - renderedData.startTime + renderedData.fudgeFactor) <= fractal.minFPS) && (i < size)) {
                renderedData.incomplete = true;
                fill();
                break;
            }
        }
        if (isVerticalSymmetrySupported || isHorizontalSymmetrySupported) {
            doSymmetry(renderedData.reallocX, renderedData.reallocY);
        }
        copy();
    }

    /** Process the reallocation table
     *
     */
    function processReallocTable() {
        var total = 0;
        renderedData.incomplete = false;
        total = initPrices(renderedData.queue, total, renderedData.reallocX);
        total = initPrices(renderedData.queue, total, renderedData.reallocY);
        if (total > 0) {
            if (total > 1) {
                sortQueue(renderedData.queue, 0, total - 1);
            }
            processQueue(total);
        }
    }

    /** Swap new and old buffers
     *
     */
    function swapBuffers() {
        var tmp = renderedData.oldBuffer;
        renderedData.oldBuffer = renderedData.newBuffer;
        renderedData.newBuffer = tmp;
        tmp = renderedData.oldImage;
        renderedData.newImage = renderedData.oldImage;
        renderedData.oldImage = tmp;
    }

    /** Update position array with newly calculated positions
     *
     */
    function updatePosition() {
        var k;
        var len;
        for (k = 0,len = renderedData.reallocX.length; k < len; k++) {
            renderedData.positionX[k] = renderedData.reallocX[k].position;
        }
        for (k = 0,len = renderedData.reallocY.length; k < len; k++) {
            renderedData.positionY[k] = renderedData.reallocY[k].position;
        }
    }

    /** Prepare reallocation table for lines
     *
     */
    function prepareLines() {
        var beginy = area.begin.y;
        var endy = area.end.y;
        var stepy = 0;
        var symy;
        if (((renderMode & MODE_CALCULATE) === 0) && USE_XAOS) {
            stepy = makeReallocTable(renderedData.reallocY, renderedData.dynamicY, beginy, endy, renderedData.positionY);
        } else {
            stepy = initReallocTableAndPosition(renderedData.reallocY, renderedData.positionY, beginy, endy, true);
        }
        symy = fractal.symmetry && fractal.symmetry.y;
        if (isVerticalSymmetrySupported && !((beginy > symy) || (symy > endy))) {
            prepareSymmetry(renderedData.reallocY, Math.floor((symy - beginy) / stepy), symy, stepy);
        }
    }

    /** Prepare reallocation table for columns
     *
     */
    function prepareColumns() {
        var beginx = area.begin.x;
        var endx = area.end.x;
        var stepx = 0;
        var symx;
        if (((renderMode & MODE_CALCULATE) === 0) && USE_XAOS) {
            stepx = makeReallocTable(renderedData.reallocX, renderedData.dynamicX, beginx, endx, renderedData.positionX);
        } else {
            stepx = initReallocTableAndPosition(renderedData.reallocX, renderedData.positionX, beginx, endx, false);
        }
        symx = fractal.symmetry && fractal.symmetry.x;
        if (isHorizontalSymmetrySupported && (!((beginx > symx) || (symx > endx)))) {
            prepareSymmetry(renderedData.reallocX, Math.floor((symx - beginx) / stepx), symx, stepx);
        }
    }

    /** Overall fractal drawing workflow, calls other functions
     *
     */
    function drawFractal() {
        renderedData.startTime = new Date().getTime();
        swapBuffers();
        prepareLines();
        prepareColumns();
        move();
        processReallocTable();
        updatePosition();
        renderMode = 0;
        var fps = 1000 / (new Date().getTime() - renderedData.startTime);
        if (fps < fractal.minFPS) {
            renderedData.fudgeFactor++;
        } else if (fps > fractal.minFPS + 10 && renderedData.fudgeFactor > 0) {
            renderedData.fudgeFactor--;
        }
        console.log(fps + " fps");
    }

    /** Adjust display region to zoom based on mouse buttons
     *
     * @returns {boolean}
     */
    function updateRegion() {
        var MAXSTEP = 0.008 * 3;
        //var STEP = 0.0006*3;
        var MUL = 0.3;
        area = convertArea();
        var x = area.begin.x + mouse.x * ((area.end.x - area.begin.x) / canvas.width);
        var y = area.begin.y + mouse.y * ((area.end.y - area.begin.y) / canvas.height);
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
            return false;
        }
        mmul = Math.pow((1 - step), MUL);
        area.begin.x = x + (area.begin.x - x) * mmul;
        area.end.x = x + (area.end.x - x) * mmul;
        area.begin.y = y + (area.begin.y - y) * mmul;
        area.end.y = y + (area.end.y - y) * mmul;
        fractal.region.radius.x = area.end.x - area.begin.x;
        fractal.region.radius.y = area.end.y - area.begin.y;
        fractal.region.center.x = (area.begin.x + area.end.x) / 2;
        fractal.region.center.y = ((area.begin.y + area.end.y) / 2) * (canvas.width / canvas.height);
        return true;
    }

    /** Draw the fractal and request the next animation frame
     *
     */
    function doZoom() {
        if (updateRegion() || renderedData.incomplete) {
            requestAnimationFrame(doZoom);
            drawFractal();
        }
    }

    canvas.onmousedown = function(e) {
        mouse.button[e.button] = true;
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

    drawFractal();
};

xaos.makePalette = function() {
    var MAXENTRIES = 65536,
        segmentsize,
        setsegments,
        nsegments,
        i, y,
        r, g, b,
        rs, gs, bs,
        palette = [],
        segments = [
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
    segmentsize = 8;
    nsegments = Math.floor(255 / segmentsize);
    setsegments = Math.floor((MAXENTRIES + 3) / segmentsize);

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

var fractal = {
    symmetry: {x: null, y: 0 },
    region: {
        center: { x: -0.75, y: 0.0 },
        radius: { x: 2.5, y : 2.5 },
        angle: 0
    },
    z0: { x: 0, y: 0 },
    maxiter: 512,
    bailout: 4,
    minFPS: 60,
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
    palette: xaos.makePalette()
};

xaos.zoom(document.getElementById("canvas"), fractal);