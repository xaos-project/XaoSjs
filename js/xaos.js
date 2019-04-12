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
    var USE_XAOS = true,
        USE_SYMMETRY = false,
        USE_SOLIDGUESS = true,
        RANGES = 2,
        RANGE = 4,
        MASK = 0x7,
        DSIZE = (RANGES + 1),
        FPMUL = 64,
        IRANGE = FPMUL * RANGE,
        MAX_PRICE = Number.MAX_VALUE,
        NEW_PRICE = IRANGE * IRANGE,
        GUESS_RANGE = 4;

    /** Utility function to pre-allocate an array of the specified size
     * with the specified initial value. It will do the right thing
     * to create unique items, whether you pass in a prototype, a
     * constructor, or a primitive.
     * @param {number} size - the size of the array.
     * @param initial - the initial value for each entry.
     */
    function preAllocArray(size, initial) {
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
     * @param vector
     * @param r1
     * @param r2
     */
    function addPrices(vector, r1, r2) {
        var r3;
        while (r1 < r2) {
            r3 = r1 + ((r2 - r1) >> 1);
            vector[r3].priority = (vector[r2].position - vector[r3].position) * vector[r3].priority;
            if (vector[r3].symRef !== -1) {
                vector[r3].priority /= 2.0;
            }
            addPrices(vector, r1, r3);
            r1 = r3 + 1;
        }
    }

    /** Initialize prices from relocation table
     *
     * @param queue
     * @param total
     * @param vector
     * @returns {*}
     */
    function initPrices(queue, total, vector) {
        var i;
        var j = 0;
        for (i = 0; i < vector.length; i++) {
            if (vector[i].recalculate) {
                for (j = i; (j < vector.length) && vector[j].recalculate; j++) {
                    queue[total++] = vector[j];
                }
                if (j === vector.length) {
                    j -= 1;
                }
                addPrices(vector, i, j);
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

    /** Creates a single entry for a move or fill table.
     * @constructor
     */
    function TableEntry() {
        this.length = 0;
        this.from = 0;
        this.to = 0;
    }

    /** Creates a single entry for a this data table.
     * @constructor
     */
    function DynamicEntry() {
        this.previous = null;
        this.pos = 0;
        this.price = MAX_PRICE;
    }

    /** Creates a single entry for a relocation table.
     * @constructor
     */
    function Vector() {
        this.recalculate = false;
        this.dirty = false;
        this.line = false;
        this.pos = 0;
        this.plus = 0;
        this.symTo = 0;
        this.symRef = 0;
        this.lastPosition = 0.0;
        this.position = 0.0;
        this.priority = 0.0;
    }

    function CanvasImage(canvas) {
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

    /** Container for all zoom context data for a particular canvas.
     *
     * @param image {CanvasImage} Image on which to draw the fractal.
     * @param fractal {FractalContext} Fractal parameters.
     * @constructor
     */
    function ZoomContext(image, fractal) {
        var size = Math.max(canvas.width, canvas.height);
        this.image = image;
        this.fractal = fractal;
        this.columns = preAllocArray(canvas.width, Vector);
        this.rows = preAllocArray(canvas.height, Vector);
        this.delta = preAllocArray(size + 1, 0);
        this.oldBest = preAllocArray(size, DynamicEntry);
        this.newBest = preAllocArray(size, DynamicEntry);
        this.calData = preAllocArray(size, DynamicEntry);
        this.conData = preAllocArray(size << DSIZE, DynamicEntry);
        this.moveTable = preAllocArray(canvas.width + 1, TableEntry);
        this.fillTable = preAllocArray(canvas.width + 1, TableEntry);
        this.queue = preAllocArray(canvas.width + canvas.height, null);
        this.startTime = 0;
        this.minFPS = 60;
        this.fudgeFactor = 0;
        this.incomplete = false;
        this.zooming = false;
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

    /** Resets relocation table for fresh calculation
     *
     * @param vector - relocation table
     * @param position - array of coordinates for line or column in the complex plane
     * @param begin - starting cooridnate
     * @param end - ending coordinate
     * @param line - whether this is a line or column
     * @returns {number}
     */
    ZoomContext.prototype.initVector = function(vector, begin, end, line) {
        var i, p, step = (end - begin) / vector.length;
        for (i = 0, p = begin; i < vector.length; i++, p += step) {
            vector[i].recalculate = true;
            vector[i].dirty = true;
            vector[i].line = line;
            vector[i].pos = i;
            vector[i].lastPosition = p;
            vector[i].position = p;
            vector[i].plus = i;
            vector[i].symTo = -1;
            vector[i].symRef = -1;
        }
        return step;
    }

    /** Calculate the best approximation for points based on previous frame
     *
     * @param vector - relocation table for rows or columns
     * @param begin - beginning coordinate (x or y)
     * @param end - ending coordinate (x or y)
     * @param position - array of position coordinates on the complex plane
     * @returns {number}
     */
    ZoomContext.prototype.updateVector = function(vector, begin, end) {
        var previous = null;
        var best = null;
        var price = 0;
        var i;
        var y = 0;
        var p = 0;
        var ps = 0;
        var pe = 0;
        var ps1 = 0;
        var yend = 0;
        var flag = 0;
        var size = vector.length;
        var step = (end - begin) / size;
        var tofix = (size * FPMUL) / (end - begin);
        var delta = this.delta;

        delta[size] = Number.MAX_VALUE;
        for (i = size - 1; i >= 0; i--) {
            delta[i] = ((vector[i].lastPosition - begin) * tofix) | 0;
            if (delta[i] > delta[i + 1]) {
                delta[i] = delta[i + 1];
            }
        }

        for (i = 0; i < size; i++) {
            this.swapBest();
            yend = y - IRANGE;
            if (yend < 0) {
                yend = 0;
            }
            p = ps;
            while (delta[p] < yend) {
                p++;
            }
            ps1 = p;
            yend = y + IRANGE;

            if ((ps !== pe) && (p > ps)) {
                if (p < pe) {
                    previous = this.oldBest[p - 1];
                } else {
                    previous = this.oldBest[pe - 1];
                }
                price = previous.price;
            } else if (i > 0) {
                previous = this.calData[i - 1];
                price = previous.price;
            } else {
                previous = null;
                price = 0;
            }

            price += NEW_PRICE;
            best = this.calData[i];
            best.price = price;
            best.pos = -1;
            best.previous = previous;

            if (ps !== pe) {
                if (p === ps) {
                    if (delta[p] !== delta[p + 1]) {
                        previous = this.calData[i - 1];
                        price = previous.price + calcPrice(delta[p], y);
                        if (price < best.price) {
                            best = this.conData[(p << DSIZE) + (i & MASK)];
                            best.price = price;
                            best.pos = p;
                            best.previous = previous;
                        }
                    }
                    this.newBest[p++] = best;
                }
                previous = null;
                while (p < pe) {
                    if (delta[p] !== delta[p + 1]) {
                        previous = this.oldBest[p - 1];
                        price = previous.price + NEW_PRICE;
                        if (price < best.price) {
                            best = this.conData[((p - 1) << DSIZE) + (i & MASK)];
                            best.price = price;
                            best.pos = -1;
                            best.previous = previous;
                            this.newBest[p - 1] = best;
                        }
                        price = previous.price + calcPrice(delta[p], y);
                        if (price < best.price) {
                            best = this.conData[(p << DSIZE) + (i & MASK)];
                            best.price = price;
                            best.pos = p;
                            best.previous = previous;
                        } else if (delta[p] > y) {
                            this.newBest[p++] = best;
                            break;
                        }
                    }
                    this.newBest[p++] = best;
                }
                if (p > ps) {
                    previous = this.oldBest[p - 1];
                } else {
                    previous = this.calData[i - 1];
                }
                price = previous.price + NEW_PRICE;
                if ((price < best.price) && (p > ps1)) {
                    best = this.conData[((p - 1) << DSIZE) + (i & MASK)];
                    best.price = price;
                    best.pos = -1;
                    best.previous = previous;
                    this.newBest[p - 1] = best;
                }
                while (delta[p] < yend) {
                    if (delta[p] !== delta[p + 1]) {
                        price = previous.price + calcPrice(delta[p], y);
                        if (price < best.price) {
                            best = this.conData[(p << DSIZE) + (i & MASK)];
                            best.price = price;
                            best.pos = p;
                            best.previous = previous;
                        } else if (delta[p] > y) {
                            break;
                        }
                    }
                    this.newBest[p++] = best;
                }
                while (delta[p] < yend) {
                    this.newBest[p++] = best;
                }
            } else if (delta[p] < yend) {
                if (i > 0) {
                    previous = this.calData[i - 1];
                    price = previous.price;
                } else {
                    previous = null;
                    price = 0;
                }
                while (delta[p] < yend) {
                    if (delta[p] !== delta[p + 1]) {
                        price += calcPrice(delta[p], y);
                        if (price < best.price) {
                            best = this.conData[(p << DSIZE) + (i & MASK)];
                            best.price = price;
                            best.pos = p;
                            best.previous = previous;
                        } else if (delta[p] > y) {
                            break;
                        }
                    }
                    this.newBest[p++] = best;
                }
                while (delta[p] < yend) {
                    this.newBest[p++] = best;
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
            vector[i].symTo = -1;
            vector[i].symRef = -1;
            if (best.pos < 0) {
                vector[i].recalculate = true;
                vector[i].dirty = true;
                vector[i].plus = vector[i].pos;
            } else {
                vector[i].plus = best.pos;
                vector[i].position = vector[best.pos].lastPosition;
                vector[i].recalculate = false;
                vector[i].dirty = false;
            }
            best = best.previous;
        }
        newPositions(vector, begin, end, step, flag);
        return step;
    }

    /** Calculate new positions based on relocation table
     *
     * @param vector
     * @param size
     * @param begin1
     * @param end1
     * @param step
     * @param position
     * @param flag
     */
    function newPositions(vector, begin1, end1, step, flag) {
        var delta = 0;
        var size = vector.length;
        var begin = 0;
        var end = 0;
        var s = -1;
        var e = -1;
        if (begin1 > end1) {
            begin1 = end1;
        }
        while (s < (size - 1)) {
            e = s + 1;
            if (vector[e].recalculate) {
                while (e < size) {
                    if (!vector[e].recalculate) {
                        break;
                    }
                    e++;
                }
                if (e < size) {
                    end = vector[e].position;
                } else {
                    end = end1;
                }
                if (s < 0) {
                    begin = begin1;
                } else {
                    begin = vector[s].position;
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
                            vector[s].position = begin;
                            vector[s].priority = 1 / (1 + (Math.abs((vector[s].lastPosition - begin)) * step));
                        }
                        break;
                    case 2:
                        for (s++; s < e; s++) {
                            begin += delta;
                            vector[s].position = begin;
                            vector[s].priority = Math.abs((vector[s].lastPosition - begin)) * step;
                        }
                        break;
                    default:
                        for (s++; s < e; s++) {
                            begin += delta;
                            vector[s].position = begin;
                            vector[s].priority = 1.0;
                        }
                        break;
                }
            }
            s = e;
        }
    }

    /** Populate symmetry data into relocation table
     *
     * @param vector
     * @param symi
     * @param symPosition
     * @param step
     */
    ZoomContext.prototype.prepareSymmetry = function(vector, symi, symPosition, step) {
        var i;
        var j = 0;
        var tmp;
        var abs;
        var distance;
        var position;
        var size = vector.length;
        var max = size - RANGE - 1;
        var min = RANGE;
        var istart = 0;
        var symRealloc = null;
        var symj = (2 * symi) - size;
        symPosition *= 2;
        if (symj < 0) {
            symj = 0;
        }
        distance = step * RANGE;
        for (i = symj; i < symi; i++) {
            if (vector[i].symTo !== -1) {
                continue;
            }
            position = vector[i].position;
            vector[i].symTo = (2 * symi) - i;
            if (vector[i].symTo > max) {
                vector[i].symTo = max;
            }
            j = ((vector[i].symTo - istart) > RANGE) ? (-RANGE) : (-vector[i].symTo + istart);
            if (vector[i].recalculate) {
                while ((j < RANGE) && ((vector[i].symTo + j) < (size - 1))) {
                    tmp = symPosition - vector[vector[i].symTo + j].position;
                    abs = Math.abs(tmp - position);
                    if (abs < distance) {
                        if (((i === 0) || (tmp > vector[i - 1].position)) && (tmp < vector[i + 1].position)) {
                            distance = abs;
                            min = j;
                        }
                    } else if (tmp < position) {
                        break;
                    }
                    j++;
                }
            } else {
                while ((j < RANGE) && ((vector[i].symTo + j) < (size - 1))) {
                    if (vector[i].recalculate) {
                        tmp = symPosition - vector[vector[i].symTo + j].position;
                        abs = Math.abs(tmp - position);
                        if (abs < distance) {
                            if (((i === 0) || (tmp > vector[i - 1].position)) && (tmp < vector[i + 1].position)) {
                                distance = abs;
                                min = j;
                            }
                        } else if (tmp < position) {
                            break;
                        }
                    }
                    j++;
                }
            }
            vector[i].symTo += min;
            symRealloc = vector[vector[i].symTo];
            if ((min === RANGE) || (vector[i].symTo <= symi) || (symRealloc.symTo !== -1) || (symRealloc.symRef !== -1)) {
                vector[i].symTo = -1;
                continue;
            }
            if (!vector[i].recalculate) {
                vector[i].symTo = -1;
                if ((symRealloc.symTo !== -1) || !symRealloc.recalculate) {
                    continue;
                }
                symRealloc.plus = vector[i].plus;
                symRealloc.symTo = i;
                istart = vector[i].symTo - 1;
                symRealloc.recalculate = false;
                symRealloc.dirty = true;
                vector[i].symRef = vector[i].symTo;
                symRealloc.position = symPosition - vector[i].position;
            } else {
                if (symRealloc.symTo !== -1) {
                    vector[i].symTo = -1;
                    continue;
                }
                vector[i].plus = symRealloc.plus;
                istart = vector[i].symTo - 1;
                vector[i].recalculate = false;
                vector[i].dirty = true;
                symRealloc.symRef = i;
                vector[i].position = symPosition - symRealloc.position;
            }
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
        var tmp = null;
        var i = 0;
        var j = 0;
        var s = 0;
        while (i < this.columns.length) {
            if (!this.columns[i].dirty) {
                tmp = this.moveTable[s];
                tmp.to = i;
                tmp.length = 1;
                tmp.from = this.columns[i].plus;
                for (j = i + 1; j < this.columns.length; j++) {
                    if (this.columns[j].dirty || ((j - this.columns[j].plus) !== (tmp.to - tmp.from))) {
                        break;
                    }
                    tmp.length++;
                }
                i = j;
                s++;
            } else {
                i++;
            }
        }
        tmp = this.moveTable[s];
        tmp.length = 0;
    }

    /** Execute moves defined in move table */
    ZoomContext.prototype.doMove = function() {
        var tmp = null;
        var new_offset = 0;
        var old_offset = 0;
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
                old_offset = this.rows[i].plus * bufferWidth;
                while ((tmp = this.moveTable[s]).length > 0) {
                    from = old_offset + tmp.from;
                    to = new_offset + tmp.to;
                    length = tmp.length;
                    arrayCopy(oldBuffer, from, newBuffer, to, length);
                    s++;
                }
            }
            new_offset += bufferWidth;
        }
    }

    /** Shortcut for prepare and execute move */
    ZoomContext.prototype.move = function() {
        this.prepareMove();
        this.doMove();
    };

    /** Prepare fill table based on relocation table */
    ZoomContext.prototype.prepareFill = function() {
        var tmp = null;
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
                    if ((k < this.columns.length) && ((j < i) || ((this.columns[i].position - this.columns[j].position) > (this.columns[k].position - this.columns[i].position)))) {
                        j = k;
                    } else if (j < 0) {
                        break;
                    }
                    n = k - i;
                    tmp = this.fillTable[s];
                    tmp.length = n;
                    tmp.from = j;
                    tmp.to = i;
                    while (n > 0) {
                        this.columns[i].position = this.columns[j].position;
                        this.columns[i].dirty = false;
                        n--;
                        i++;
                    }
                    s++;
                }
            }
        }
        tmp = this.fillTable[s];
        tmp.length = 0;
    }

    /** Apply fill table */
    ZoomContext.prototype.doFill = function() {
        var tmp = null;
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
                    if ((k < this.rows.length) && ((j < i) || ((this.rows[i].position - this.rows[j].position) > (this.rows[k].position - this.rows[i].position)))) {
                        j = k;
                    } else if (j < 0) {
                        break;
                    }
                    to_offset = i * bufferWidth;
                    from_offset = j * bufferWidth;
                    if (!this.rows[j].dirty) {
                        s = 0;
                        while ((tmp = this.fillTable[s]).length > 0) {
                            from = from_offset + tmp.from;
                            to = from_offset + tmp.to;
                            for (t = 0; t < tmp.length; t++) {
                                d = to + t;
                                buffer[d] = buffer[from];
                            }
                            s++;
                        }
                    }
                    arrayCopy(buffer, from_offset, buffer, to_offset, bufferWidth);
                    this.rows[i].position = this.rows[j].position;
                    this.rows[i].dirty = true;
                    i++;
                }
            } else {
                s = 0;
                from_offset = i * bufferWidth;
                while ((tmp = this.fillTable[s]).length > 0) {
                    from = from_offset + tmp.from;
                    to = from_offset + tmp.to;
                    for (t = 0; t < tmp.length; t++) {
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
    };

    /** Render line using solid guessing
     *
     * @param vector
     */
    ZoomContext.prototype.renderLine = function(vector) {
        var buffer = this.image.newBuffer;
        var bufferWidth = this.image.width;
        var position = vector.position;
        var r = vector.pos;
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
                    buffer[offset] = fractal.formula(current.position, position);
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
                            buffer[offset] = fractal.formula(current.position, position);
                        }
                    } else {
                        buffer[offset] = fractal.formula(current.position, position);
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
        vector.recalculate = false;
        vector.dirty = false;
    }

    /** Render column using solid guessing
     *
     * @param vector
     */
    ZoomContext.prototype.renderColumn = function(vector) {
        var buffer = this.image.newBuffer;
        var bufferWidth = this.image.width;
        var position = vector.position;
        var r = vector.pos;
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
                    buffer[offset] = fractal.formula(position, current.position);
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
                            buffer[offset] = fractal.formula(position, current.position);
                        }
                    } else {
                        buffer[offset] = fractal.formula(position, current.position);
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
        vector.recalculate = false;
        vector.dirty = false;
    }

    /** Calculate whether we're taking too long to render the fractal to meet the target FPS */
    ZoomContext.prototype.tooSlow = function() {
        var newTime = new Date().getTime(),
            minFPS = this.zooming ? this.minFPS : 10;
        return 1000 / (newTime - this.startTime + this.fudgeFactor) < minFPS;
    };

    /** Process the relocation table */
    ZoomContext.prototype.calculate = function() {
        var i, newTime, total = 0;
        this.incomplete = false;
        total = initPrices(this.queue, total, this.columns);
        total = initPrices(this.queue, total, this.rows);
        if (total > 0) {
            if (total > 1) {
                sortQueue(this.queue, 0, total - 1);
            }
            for (i = 0; i < total; i++) {
                if (this.queue[i].line) {
                    this.renderLine(this.queue[i]);
                } else {
                    this.renderColumn(this.queue[i]);
                }
                if (!this.recalculate && this.tooSlow() && (i < total)) {
                    this.incomplete = true;
                    this.fill();
                    break;
                }
            }
        }
    };

    /** Update position array with newly calculated positions */
    ZoomContext.prototype.updatePosition = function() {
        var k;
        var len;
        for (k = 0,len = this.columns.length; k < len; k++) {
            this.columns[k].lastPosition = this.columns[k].position;
        }
        for (k = 0,len = this.rows.length; k < len; k++) {
            this.rows[k].lastPosition = this.rows[k].position;
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
        var area = this.convertArea(),
            symx = this.fractal.symmetry && this.fractal.symmetry.x,
            symy = this.fractal.symmetry && this.fractal.symmetry.y,
            stepx, stepy;
        this.startTime = new Date().getTime();
        this.recalculate = recalculate;
        if (recalculate || !USE_XAOS) {
            stepx = this.initVector(this.columns, area.begin.x, area.end.x, false);
            stepy = this.initVector(this.rows, area.begin.y, area.end.y, true);
        } else {
            stepx = this.updateVector(this.columns, area.begin.x, area.end.x);
            stepy = this.updateVector(this.rows, area.begin.y, area.end.y);
        }
        if (USE_SYMMETRY && typeof symy === "number" && !(area.begin.y > symy || symy > area.end.y)) {
            this.prepareSymmetry(this.rows, Math.floor((symy - area.begin.y) / stepy), symy, stepy);
        }
        if (USE_SYMMETRY && typeof symx === "number" && !(area.begin.x > symx || symx > area.end.x)) {
            this.prepareSymmetry(this.columns, Math.floor((symx - area.begin.x) / stepx), symx, stepx);
        }
        this.image.swapBuffers();
        this.move();
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

        canvas.onmousedown = function(e) {
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