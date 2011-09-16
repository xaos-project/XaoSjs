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

Function.prototype.curry = function () {
    var slice = Array.prototype.slice,
        args = slice.apply(arguments),
        that = this;
    return function () {
        return that.apply(null, args.concat(slice.apply(arguments)));
    };
};
xaos.zoom = function(canvas, fractal) {
    "use strict";
    var MODE_CALCULATE = 0x01,
        MODE_REFRESH = 0x02,
        USE_XAOS = true,
        USE_SYMMETRY = false,
        RANGES = 2,
        RANGE = 4,
        STEPS = 8,
        MASK = 0x7,
        DSIZE = (RANGES + 1),
        FPMUL = 64,
        FPRANGE = FPMUL * RANGE,
        MAX_PRICE = Number.MAX_VALUE,
        NEW_PRICE = FPRANGE * FPRANGE,
        mouse = { x: 0, y: 0, button: [false, false, false] },
        renderPoint = fractal.formula.curry(fractal.palette),
        context = canvas.getContext("2d"),
        bufferWidth = canvas.width * 4,
        renderMode = 0;
    var renderedData = (function() {
        var initArray = function(size, initial) {
            var data = [], i;
            for (i = 0; i < size; i += 1) {
                data[i] = typeof initial === "object" ? Object.create(initial) : initial;
            }
            return data;
        };
        var initTable = function(size) {
            var prototype = {
                length : 0,
                from : 0,
                to : 0
            };
            return initArray(size, prototype);
        };
        var initDynamic = function(size) {
            var prototype = {
                previous : null,
                pos : 0,
                price : 0
            };
            return {
                delta : initArray(size + 1, 0),
                oldBest : initArray(size, prototype),
                newBest : initArray(size, prototype),
                calData : initArray(size, prototype),
                conData : initArray(size << DSIZE, prototype),
                swap: function() {
                    var tmpBest = this.oldBest;
                    this.oldBest = this.newBest;
                    this.newBest = tmpBest;
                }
            };
        };
        var initRealloc = function(size, line) {
            var prototype, data, i;
            prototype = {
                refreshed : false,
                recalculate : false,
                changeDirty : false,
                dirty : false,
                line : line,
                pos : 0,
                plus : 0,
                symTo : 0,
                symRef : 0,
                changePosition : 0,
                position : 0,
                priority : 0
            };
            data = initArray(size, prototype);
            for (i = 0; i < size; i++) {
                data[i].pos = i;
            }
            return data;
        };
        return {
            newBuffer : context.createImageData(canvas.width, canvas.height),
            oldBuffer : context.createImageData(canvas.width, canvas.height),
            positionX : initArray(canvas.width, 0),
            positionY : initArray(canvas.height, 0),
            reallocX : initRealloc(canvas.width, false),
            reallocY : initRealloc(canvas.height, true),
            dynamicX : initDynamic(canvas.width),
            dynamicY : initDynamic(canvas.height),
            moveTable : initTable(canvas.width + 1),
            fillTable : initTable(canvas.width + 1),
            queue : initRealloc(canvas.width + canvas.height, false),
            x0 : 0,
            y0 : 0,
            newTime : 0,
            oldTime : 0,
            position : initArray(STEPS, 0),
            offset : initArray(STEPS, 0)
        };
    }());

    var convertArea = function() {
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
    };

    var drawFractal = function(dynamic) {
        var start = new Date().getTime();
        var isAborted = false;
        var isInterrupted = false;
        var percent = 0;
        var area = convertArea();

        var isVerticalSymmetrySupported = (USE_SYMMETRY && fractal.symmetry && typeof fractal.symmetry.y === "number") || false;
        var isHorizontalSymmetrySupported = (USE_SYMMETRY && fractal.symmetry && typeof fractal.symmetry.x === "number") || false;

        var makeReallocTable = function(realloc, dynamic, begin, end, position) {
            var tmpRealloc = null;
            var prevData = null;
            var bestData = null;
            var tmpData = null;
            var bestPrice = MAX_PRICE;
            var price = 0;
            var price1 = 0;
            var i = 0;
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
                delta[i] = Math.floor((position[i] - begin) * tofix);
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
                    }
                    else {
                        prevData = dynamic.oldBest[pe - 1];
                    }
                    price1 = prevData.price;
                }
                else {
                    if (i > 0) {
                        prevData = dynamic.calData[i - 1];
                        price1 = prevData.price;
                    }
                    else {
                        prevData = null;
                        price1 = 0;
                    }
                }
                tmpData = dynamic.calData[i];
                price = price1 + NEW_PRICE;
                bestData = tmpData;
                bestPrice = price;
                tmpData.price = price;
                tmpData.pos = -1;
                tmpData.previous = prevData;
                if (ps !== pe) {
                    if (p === ps) {
                        if (delta[p] !== delta[p + 1]) {
                            prevData = dynamic.calData[i - 1];
                            price1 = prevData.price;
                            price = price1 + calcPrice(delta[p], y);
                            if (price < bestPrice) {
                                tmpData = dynamic.conData[(p << DSIZE) + (i & MASK)];
                                bestData = tmpData;
                                bestPrice = price;
                                tmpData.price = price;
                                tmpData.pos = p;
                                tmpData.previous = prevData;
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
                                tmpData = dynamic.conData[((p - 1) << DSIZE) + (i & MASK)];
                                bestData = tmpData;
                                bestPrice = price;
                                tmpData.price = price;
                                tmpData.pos = -1;
                                tmpData.previous = prevData;
                                dynamic.newBest[p - 1] = bestData;
                            }
                            price = price1 + calcPrice(delta[p], y);
                            if (price < bestPrice) {
                                tmpData = dynamic.conData[(p << DSIZE) + (i & MASK)];
                                bestData = tmpData;
                                bestPrice = price;
                                tmpData.price = price;
                                tmpData.pos = p;
                                tmpData.previous = prevData;
                            }
                            else if (delta[p] > y) {
                                dynamic.newBest[p++] = bestData;
                                break;
                            }
                        }
                        dynamic.newBest[p++] = bestData;
                    }
                    while (p < pe) {
                        if (delta[p] !== delta[p + 1]) {
                            prevData = dynamic.oldBest[p - 1];
                            price1 = prevData.price;
                            price = price1 + NEW_PRICE;
                            if (price < bestPrice) {
                                tmpData = dynamic.conData[((p - 1) << DSIZE) + (i & MASK)];
                                bestData = tmpData;
                                bestPrice = price;
                                tmpData.price = price;
                                tmpData.pos = -1;
                                tmpData.previous = prevData;
                                dynamic.newBest[p - 1] = bestData;
                            }
                            price = price1 + calcPrice(delta[p], y);
                            if (price < bestPrice) {
                                tmpData = dynamic.conData[(p << DSIZE) + (i & MASK)];
                                bestData = tmpData;
                                bestPrice = price;
                                tmpData.price = price;
                                tmpData.pos = p;
                                tmpData.previous = prevData;
                            }
                        }
                        dynamic.newBest[p++] = bestData;
                    }
                    if (p > ps) {
                        prevData = dynamic.oldBest[p - 1];
                        price1 = prevData.price;
                    }
                    else {
                        prevData = dynamic.calData[i - 1];
                        price1 = prevData.price;
                    }
                    price = price1 + NEW_PRICE;
                    if ((price < bestPrice) && (p > ps1)) {
                        tmpData = dynamic.conData[((p - 1) << DSIZE) + (i & MASK)];
                        bestData = tmpData;
                        bestPrice = price;
                        tmpData.price = price;
                        tmpData.pos = -1;
                        tmpData.previous = prevData;
                        dynamic.newBest[p - 1] = bestData;
                    }
                    while (delta[p] < yend) {
                        if (delta[p] !== delta[p + 1]) {
                            price = price1 + calcPrice(delta[p], y);
                            if (price < bestPrice) {
                                tmpData = dynamic.conData[(p << DSIZE) + (i & MASK)];
                                bestData = tmpData;
                                bestPrice = price;
                                tmpData.price = price;
                                tmpData.pos = p;
                                tmpData.previous = prevData;
                            }
                            else if (delta[p] > y) {
                                break;
                            }
                        }
                        dynamic.newBest[p++] = bestData;
                    }
                    while (delta[p] < yend) {
                        dynamic.newBest[p++] = bestData;
                    }
                }
                else {
                    if (delta[p] < yend) {
                        if (i > 0) {
                            prevData = dynamic.calData[i - 1];
                            price1 = prevData.price;
                        }
                        else {
                            prevData = null;
                            price1 = 0;
                        }
                        while (delta[p] < yend) {
                            if (delta[p] !== delta[p + 1]) {
                                price = price1 + calcPrice(delta[p], y);
                                if (price < bestPrice) {
                                    tmpData = dynamic.conData[(p << DSIZE) + (i & MASK)];
                                    bestData = tmpData;
                                    bestPrice = price;
                                    tmpData.price = price;
                                    tmpData.pos = p;
                                    tmpData.previous = prevData;
                                }
                                else if (delta[p] > y) {
                                    break;
                                }
                            }
                            dynamic.newBest[p++] = bestData;
                        }
                        while (delta[p] < yend) {
                            dynamic.newBest[p++] = bestData;
                        }
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
                tmpData = bestData.previous;
                tmpRealloc = realloc[i];
                tmpRealloc.symTo = -1;
                tmpRealloc.symRef = -1;
                if (bestData.pos < 0) {
                    tmpRealloc.recalculate = true;
                    tmpRealloc.refreshed = false;
                    tmpRealloc.dirty = true;
                    tmpRealloc.plus = tmpRealloc.pos;
                }
                else {
                    tmpRealloc.plus = bestData.pos;
                    tmpRealloc.position = position[bestData.pos];
                    tmpRealloc.recalculate = false;
                    tmpRealloc.refreshed = false;
                    tmpRealloc.dirty = false;
                }
                bestData = tmpData;
            }
            newPositions(realloc, size, begin, end, step, position, flag);
            return step;
        };

        var initReallocTableAndPosition = function(realloc, position, begin, end) {
            var step = (end - begin) / realloc.length;
            var tmpPosition = begin;
            var tmpRealloc = null;
            var i;
            for (i = 0; i < realloc.length; i++) {
                tmpRealloc = realloc[i];
                position[i] = tmpPosition;
                tmpRealloc.position = tmpPosition;
                tmpRealloc.recalculate = true;
                tmpRealloc.refreshed = false;
                tmpRealloc.dirty = true;
                tmpRealloc.plus = i;
                tmpRealloc.symTo = -1;
                tmpRealloc.symRef = -1;
                tmpPosition += step;
            }
            return step;
        };

        var prepareSymmetry = function(realloc, symi, symPosition, step) {
            var i = 0;
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
                        }
                        else if (tmp < tmpPosition) {
                            break;
                        }
                        j += 1;
                    }
                }
                else {
                    while ((j < RANGE) && ((tmpRealloc.symTo + j) < (size - 1))) {
                        if (tmpRealloc.recalculate) {
                            tmp = symPosition - realloc[tmpRealloc.symTo + j].position;
                            abs = Math.abs(tmp - tmpPosition);
                            if (abs < distance) {
                                if (((i === 0) || (tmp > realloc[i - 1].position)) && (tmp < realloc[i + 1].position)) {
                                    distance = abs;
                                    min = j;
                                }
                            }
                            else if (tmp < tmpPosition) {
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
                    symRealloc.refreshed = false;
                    symRealloc.dirty = true;
                    tmpRealloc.symRef = tmpRealloc.symTo;
                    symRealloc.position = symPosition - tmpRealloc.position;
                }
                else {
                    if (symRealloc.symTo !== -1) {
                        tmpRealloc.symTo = -1;
                        continue;
                    }
                    tmpRealloc.plus = symRealloc.plus;
                    istart = tmpRealloc.symTo - 1;
                    tmpRealloc.recalculate = false;
                    tmpRealloc.refreshed = false;
                    tmpRealloc.dirty = true;
                    symRealloc.symRef = i;
                    tmpRealloc.position = symPosition - symRealloc.position;
                }
            }
        };

        var arrayCopy = function(from, fromOffset, to, toOffset, length) {
            while (length--) {
                to[toOffset++] = from[fromOffset++];
            }
        };

        var doSymmetry = function(reallocX, reallocY) {
            var from_offset = 0;
            var to_offset = 0;
            var i = 0;
            var j = 0;
            var newRGB = renderedData.newBuffer.data;
            for (i = 0; i < reallocY.length; i++) {
                if ((reallocY[i].symTo >= 0) && (!reallocY[reallocY[i].symTo].dirty)) {
                    from_offset = reallocY[i].symTo * bufferWidth;
                    arrayCopy(newRGB, from_offset, newRGB, to_offset, bufferWidth);
                    reallocY[i].dirty = false;
                }
                to_offset += bufferWidth;
                // TODO: Thread.yield();
            }
            for (i = 0; i < reallocX.length; i++) {
                if ((reallocX[i].symTo >= 0) && (!reallocX[reallocX[i].symTo].dirty)) {
                    to_offset = i;
                    from_offset = reallocX[i].symTo;
                    for (j = 0; j < reallocY.length; j++) {
                        newRGB[to_offset  ] = newRGB[from_offset];
                        newRGB[to_offset + 1] = newRGB[from_offset + 1];
                        newRGB[to_offset + 2] = newRGB[from_offset + 2];
                        newRGB[to_offset + 3] = newRGB[from_offset + 3];
                        to_offset += bufferWidth;
                        from_offset += bufferWidth;
                    }
                    reallocX[i].dirty = false;
                }
                // TODO: Thread.yield();
            }
        };

        var newPositions = function(realloc, size, begin1, end1, step, position, flag) {
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
                    }
                    else {
                        end = end1;
                    }
                    if (s < 0) {
                        begin = begin1;
                    }
                    else {
                        begin = realloc[s].position;
                    }
                    if ((e === size) && (begin > end)) {
                        end = begin;
                    }
                    if ((e - s) === 2) {
                        delta = (end - begin) * 0.5;
                    }
                    else {
                        delta = (end - begin) / (e - s);
                    }
                    switch (flag) {
                        case 1:
                        {
                            for (s++; s < e; s++) {
                                begin += delta;
                                tmpRealloc = realloc[s];
                                tmpRealloc.position = begin;
                                tmpRealloc.priority = 1 / (1 + (Math.abs((position[s] - begin)) * step));
                            }
                            break;
                        }
                        case 2:
                        {
                            for (s++; s < e; s++) {
                                begin += delta;
                                tmpRealloc = realloc[s];
                                tmpRealloc.position = begin;
                                tmpRealloc.priority = Math.abs((position[s] - begin)) * step;
                            }
                            break;
                        }
                        default:
                        {
                            for (s++; s < e; s++) {
                                begin += delta;
                                tmpRealloc = realloc[s];
                                tmpRealloc.position = begin;
                                tmpRealloc.priority = 1.0;
                            }
                            break;
                        }
                    }
                }
                s = e;
            }
        };

        var prepareMove = function(movetable, reallocX) {
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
                }
                else {
                    i += 1;
                }
            }
            tmpData = movetable[s];
            tmpData.length = 0;
        };

        var doMove = function(movetable, reallocY) {
            var tmpData = null;
            var new_offset = 0;
            var old_offset = 0;
            var from = 0;
            var to = 0;
            var i = 0;
            var s = 0;
            for (i = 0; i < reallocY.length; i++) {
                if (!reallocY[i].dirty) {
                    s = 0;
                    old_offset = reallocY[i].plus * bufferWidth;
                    while ((tmpData = movetable[s]).length > 0) {
                        from = old_offset + tmpData.from * 4;
                        to = new_offset + tmpData.to * 4;
                        arrayCopy(renderedData.oldBuffer.data, from, renderedData.newBuffer.data, to, tmpData.length * 4);
                        s += 1;
                    }
                }
                new_offset += bufferWidth;
                // TODO: Thread.yield();
            }
        };

        var move = function() {
            prepareMove(renderedData.moveTable, renderedData.reallocX);
            doMove(renderedData.moveTable, renderedData.reallocY);
        };

        var prepareFill = function(filltable, reallocX) {
            var tmpData = null;
            var i = 0;
            var j = 0;
            var k = 0;
            var s = 0;
            var n = 0;
            for (i = 0; i < reallocX.length; i++) {
                if (reallocX[i].dirty) {
                    j = i - 1;
                    for (k = i + 1; (k < reallocX.length) && reallocX[k].dirty; k++) {
                    }
                    while ((i < reallocX.length) && reallocX[i].dirty) {
                        if ((k < reallocX.length) && ((j < i) || ((reallocX[i].position - reallocX[j].position) > (reallocX[k].position - reallocX[i].position)))) {
                            j = k;
                        }
                        else {
                            if (j < 0) {
                                break;
                            }
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
        };

        var doFill = function(filltable, reallocY) {
            var tmpData = null;
            var from_offset = 0;
            var to_offset = 0;
            var from = 0;
            var to = 0;
            var i = 0;
            var j = 0;
            var k = 0;
            var t = 0;
            var s = 0;
            var d = 0;
            var newRGB = renderedData.newBuffer.data;
            for (i = 0; i < reallocY.length; i++) {
                if (reallocY[i].dirty) {
                    j = i - 1;
                    for (k = i + 1; (k < reallocY.length) && reallocY[k].dirty; k++) {
                    }
                    while ((i < reallocY.length) && reallocY[i].dirty) {
                        if ((k < reallocY.length) && ((j < i) || ((reallocY[i].position - reallocY[j].position) > (reallocY[k].position - reallocY[i].position)))) {
                            j = k;
                        }
                        else {
                            if (j < 0) {
                                break;
                            }
                        }
                        to_offset = i * bufferWidth;
                        from_offset = j * bufferWidth;
                        if (!reallocY[j].dirty) {
                            s = 0;
                            while ((tmpData = filltable[s]).length > 0) {
                                from = from_offset + tmpData.from * 4;
                                to = from_offset + tmpData.to * 4;
                                for (t = 0; t < tmpData.length; t++) {
                                    d = to + t * 4;
                                    newRGB[d  ] = newRGB[from  ];
                                    newRGB[d + 1] = newRGB[from + 1];
                                    newRGB[d + 2] = newRGB[from + 2];
                                    newRGB[d + 3] = newRGB[from + 3];
                                }
                                s += 1;
                            }
                        }
                        arrayCopy(renderedData.newBuffer.data, from_offset, renderedData.newBuffer.data, to_offset, bufferWidth);
                        reallocY[i].position = reallocY[j].position;
                        reallocY[i].dirty = false;
                        i += 1;
                    }
                }
                else {
                    s = 0;
                    from_offset = i * bufferWidth;
                    while ((tmpData = filltable[s]).length > 0) {
                        from = from_offset + tmpData.from * 4;
                        to = from_offset + tmpData.to * 4;
                        for (t = 0; t < tmpData.length; t++) {
                            d = to + t * 4;
                            newRGB[d  ] = newRGB[from  ];
                            newRGB[d + 1] = newRGB[from + 1];
                            newRGB[d + 2] = newRGB[from + 2];
                            newRGB[d + 3] = newRGB[from + 3];
                        }
                        s += 1;
                    }
                    reallocY[i].dirty = false;
                }
                // TODO: Thread.yield();
            }
        };

        var fill = function() {
            if (isVerticalSymmetrySupported && isHorizontalSymmetrySupported) {
                doSymmetry(renderedData.reallocX, renderedData.reallocY);
            }
            prepareFill(renderedData.fillTable, renderedData.reallocX);
            doFill(renderedData.fillTable, renderedData.reallocY);
        };

        var copy = function() {
            context.putImageData(renderedData.newBuffer, 0, 0);
        };

        var calcPrice = function(p1, p2) {
            return (p1 - p2) * (p1 - p2);
        };

        var addPrices = function(realloc, r1, r2) {
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
        };

        var initPrices = function (queue, total, realloc) {
            var i = 0;
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
        };

        var sortQueue = function(queue, l, r) {
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
        };

        var renderLine = function(realloc, reallocX) {
            var position = realloc.position;
            var r = realloc.pos;
            var offset = r * bufferWidth;
            var k;
            var len;
            var rgb;
            var x0 = renderedData.x0;
            var y0 = renderedData.y0;
            var current;
            var newRGB = renderedData.newBuffer.data;
            for (k = 0,len = reallocX.length; k < len; k++) {
                current = reallocX[k];
                if (!current.dirty) {
                    rgb = renderPoint(x0, y0, current.position, position);
                    newRGB[offset] = rgb[0];
                    newRGB[offset + 1] = rgb[1];
                    newRGB[offset + 2] = rgb[2];
                    newRGB[offset + 3] = 0xff;
                }
                offset += 4;
            }
            realloc.recalculate = false;
            realloc.refreshed = true;
            realloc.dirty = false;
        };

        var renderColumn = function(realloc, reallocY) {
            var position = realloc.position;
            var offset = realloc.pos * 4;
            var current;
            var x0 = renderedData.x0;
            var y0 = renderedData.y0;
            var k;
            var newRGB = renderedData.newBuffer.data;
            var rgb;
            var len;
            for (k = 0,len = reallocY.length; k < len; k++) {
                current = reallocY[k];
                if (!current.dirty) {
                    rgb = renderPoint(x0, y0, position, current.position);
                    newRGB[offset] = rgb[0];
                    newRGB[offset + 1] = rgb[1];
                    newRGB[offset + 2] = rgb[2];
                    newRGB[offset + 3] = 0xff;
                }
                offset += bufferWidth;
            }
            realloc.recalculate = false;
            realloc.refreshed = true;
            realloc.dirty = false;
        };

        var processQueue = function(size) {
            var i = 0;
            for (i = 0; i < size; i++) {
                if (renderedData.queue[i].line) {
                    renderLine(renderedData.queue[i], renderedData.reallocX);
                } else {
                    renderColumn(renderedData.queue[i], renderedData.reallocY);
                }
                if (isInterrupted) {
                    isAborted = true;
                    break;
                }
                //TODO: Thread.yield();
            }
        };

        var processReallocTable = function(dynamic, refresh) {
            var total;
            var position;
            var offset;
            var s;
            var i;
            var j;
            var len;
            var tocalcx;
            var tocalcy;
            var tmpRealloc;
            if (dynamic || !USE_XAOS) {
                total = 0;
                total = initPrices(renderedData.queue, total, renderedData.reallocX);
                total = initPrices(renderedData.queue, total, renderedData.reallocY);
                if (total > 0) {
                    if (total > 1) {
                        sortQueue(renderedData.queue, 0, total - 1);
                    }
                    processQueue(total);
                }
                if (USE_XAOS) {
                    processReallocTable(false, refresh);
                }
            }
            else {
                position = renderedData.position;
                offset = renderedData.offset;
                position[0] = 1;
                offset[0] = 0;
                s = 1;
                i = 0;
                j = 0;
                tocalcx = 0;
                tocalcy = 0;
                tmpRealloc = renderedData.reallocX;
                for (i = 0,len = tmpRealloc.length; i < len; i++) {
                    if (tmpRealloc[i].recalculate) {
                        tocalcx++;
                    }
                }
                tmpRealloc = renderedData.reallocY;
                for (i = 0,len = tmpRealloc.length; i < len; i++) {
                    if (tmpRealloc[i].recalculate) {
                        tocalcy++;
                    }
                }
                for (i = 1; i < STEPS; i++) {
                    position[i] = 0;
                }
                while (s < STEPS) {
                    for (i = 0; i < STEPS; i++) {
                        if (position[i] === 0) {
                            for (j = i; j < STEPS; j++) {
                                if (position[j] !== 0) {
                                    break;
                                }
                            }
                            position[offset[s] = (j + i) >> 1] = 1;
                            s += 1;
                        }
                    }
                }
                renderedData.oldTime = renderedData.newTime = new Date().getTime();
                for (s = 0; !isAborted && (s < STEPS); s++) {
                    tmpRealloc = renderedData.reallocY;
                    for (i = offset[s],len = tmpRealloc.length; !isAborted && (i < len); i += STEPS) {
                        if (tmpRealloc[i].recalculate) {
                            renderLine(tmpRealloc[i], renderedData.reallocX);
                            tocalcy -= 1;
                        }
                        if (isInterrupted) {
                            isAborted = true;
                            break;
                        }
                        //TODO: Thread.yield();

                    }
                    tmpRealloc = renderedData.reallocX;
                    for (i = offset[s],len = tmpRealloc.length; !isAborted && (i < len); i += STEPS) {
                        if (tmpRealloc[i].recalculate) {
                            renderColumn(tmpRealloc[i], renderedData.reallocY);
                            tocalcx -= 1;
                        }
                        if (isInterrupted) {
                            isAborted = true;
                            break;
                        }
                        //TODO: Thread.yield();
                    }
                    renderedData.newTime = new Date().getTime();
                    if (!isAborted && ((renderedData.newTime - renderedData.oldTime) > 50) && (s < STEPS)) {
                        tmpRealloc = renderedData.reallocY;
                        for (i = 0,len = tmpRealloc.length; i < len; i++) {
                            tmpRealloc[i].changeDirty = tmpRealloc[i].dirty;
                            tmpRealloc[i].changePosition = tmpRealloc[i].position;
                        }
                        tmpRealloc = renderedData.reallocX;
                        for (i = 0,len = tmpRealloc.length; i < len; i++) {
                            tmpRealloc[i].changeDirty = tmpRealloc[i].dirty;
                            tmpRealloc[i].changePosition = tmpRealloc[i].position;
                        }
                        percent = Math.floor(((s + 1) * 100) / STEPS);
                        fill();
                        copy();
                        //TODO: Thread.yield();
                        tmpRealloc = renderedData.reallocY;
                        for (i = 0,len = tmpRealloc.length; i < len; i++) {
                            tmpRealloc[i].dirty = tmpRealloc[i].changeDirty;
                            tmpRealloc[i].position = tmpRealloc[i].changePosition;
                        }
                        tmpRealloc = renderedData.reallocX;
                        for (i = 0,len = tmpRealloc.length; i < len; i++) {
                            tmpRealloc[i].dirty = tmpRealloc[i].changeDirty;
                            tmpRealloc[i].position = tmpRealloc[i].changePosition;
                        }
                        renderedData.oldTime = renderedData.newTime;
                    }
                }
                if (!isAborted) {
                    percent = 100;
                }
            }
            fill();
            copy();
            //TODO: Thread.yield();
        };

        var swapBuffers = function() {
            var tmpBuffer = renderedData.oldBuffer;
            renderedData.oldBuffer = renderedData.newBuffer;
            renderedData.newBuffer = tmpBuffer;
        };

        var updatePosition = function() {
            var k;
            var len;
            for (k = 0,len = renderedData.reallocX.length; k < len; k++) {
                renderedData.positionX[k] = renderedData.reallocX[k].position;
            }
            for (k = 0,len = renderedData.reallocY.length; k < len; k++) {
                renderedData.positionY[k] = renderedData.reallocY[k].position;
            }
        };

        var prepareLines = function() {
            var beginy = area.begin.y;
            var endy = area.end.y;
            var stepy = 0;
            var symy;
            if (((renderMode & MODE_CALCULATE) === 0) && USE_XAOS) {
                stepy = makeReallocTable(renderedData.reallocY, renderedData.dynamicY, beginy, endy, renderedData.positionY);
            }
            else {
                stepy = initReallocTableAndPosition(renderedData.reallocY, renderedData.positionY, beginy, endy);
            }
            symy = fractal.symmetry && fractal.symmetry.y;
            if (isVerticalSymmetrySupported && !((beginy > symy) || (symy > endy))) {
                prepareSymmetry(renderedData.reallocY, Math.floor((symy - beginy) / stepy), symy, stepy);
            }
        };

        var prepareColumns = function() {
            var beginx = area.begin.x;
            var endx = area.end.x;
            var stepx = 0;
            var symx;
            if (((renderMode & MODE_CALCULATE) === 0) && USE_XAOS) {
                stepx = makeReallocTable(renderedData.reallocX, renderedData.dynamicX, beginx, endx, renderedData.positionX);
            }
            else {
                stepx = initReallocTableAndPosition(renderedData.reallocX, renderedData.positionX, beginx, endx);
            }
            symx = fractal.symmetry && fractal.symmetry.x;
            if (isHorizontalSymmetrySupported && (!((beginx > symx) || (symx > endx)))) {
                prepareSymmetry(renderedData.reallocX, Math.floor((symx - beginx) / stepx), symx, stepx);
            }
        };

        if ((renderMode & MODE_REFRESH) !== 0) {
            renderMode |= MODE_CALCULATE;
        }
        prepareLines();
        prepareColumns();
        swapBuffers();
        move();
        processReallocTable(dynamic, false);
        updatePosition();
        renderMode = 0;
        console.log((new Date().getTime() - start) + " ms");
    };

    var updateRegion = function() {
        var MAXSTEP = 0.008 * 3;
        //var STEP = 0.0006*3;
        var MUL = 0.3;
        var area = convertArea();
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
    };

    var doZoom = function() {
        if (updateRegion()) {
            drawFractal(true);
            setTimeout(doZoom, 0);
        }
    };

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

    canvas.oncontextmenu = function(e) {
        return false;
    };

    canvas.onmouseout = function(e) {
        mouse.button = [false, false, false];
    };

    drawFractal(false);
};

xaos.makePalette = function(algorithm, seed) {
    var MAXENTRIES = 65536,
        MAXNSEGMENTS = 4096,
        QQ = 255,
        segmentsize,
        setsegments,
        nsegments,
        whitemode,
        i, y,
        r, g, b,
        rs, gs, bs,
        segments,
        palette = [];

    var random = (function () {
        var state = seed || 0;

        var random = function (i) {
            var MAXRAND = 0xffffff,
                MAGICMUL = 1103515245,
                MAGICADD = 12345;

            state = (state * MAGICMUL + MAGICADD) & MAXRAND;
            return i ? Math.floor(state / MAXRAND) * i : state;
        };
        random.reseed = function() {
            state = seed;
        };
        return random;
    }());

    var segmentAlgorithms = [
        function () {
            var i = 0;

            segments = [];
            if (whitemode) {
                segments.push([255, 255, 255]);
                for (i = 0; i < nsegments; i += 2) {
                    if (i != 0) {
                        segments.push([random() % 256, random() % 256, random() % 256]);
                    }
                    if (i + 1 < nsegments) {
                        segments.push([random() % 35, random() % 35, random() % 35]);
                    }
                }
            } else {
                for (i = 0; i < nsegments; i += 2) {
                    segments.push([random() % 35, random() % 35, random() % 35]);
                    if (i + 1 < nsegments) {
                        segments.push([random() % 256, random() % 256, random() % 256]);
                    }
                }
            }
            segments.push(segments[0]);
        },

        function () {

        },

        function () {

        }
    ];

    if (algorithm !== undefined && segmentAlgorithms[algorithm]) {
        seed = random();
        whitemode = random() % 2;
        // Make smaller segments with higher probability
        segmentsize = random(QQ / 3 + 4);
        segmentsize += random(QQ / 3 + 4);
        segmentsize += random(QQ / 3 + 4);
        segmentsize += random(QQ / 3 + 4);
        segmentsize = Math.abs(segmentsize / 2 - QQ / 3 + 3);
        if (segmentsize < 8) {
            segmentsize = 8;
        } else if (segmentsize > MAXENTRIES / 3) {
            segmentsize = MAXENTRIES / 3;
        }
        nsegments = Math.floor((MAXENTRIES + segmentsize - 5) / segmentsize);
        if (nsegments < 0) {
            nsegments = 1;
        }
        if (nsegments > MAXNSEGMENTS) {
            setsegments = MAXNSEGMENTS;
        } else {
            setsegments = nsegments;
        }
        random.reseed();
        return [];
        segmentAlgorithms[algorithm]();
    } else {
        // Use default colors
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
    }

    for (i = 0; i < setsegments; i++) {
        r = segments[i % nsegments][0];
        g = segments[i % nsegments][1];
        b = segments[i % nsegments][2];
        rs = (segments[(i + 1) % setsegments % nsegments][0] - r) / segmentsize;
        gs = (segments[(i + 1) % setsegments % nsegments][1] - g) / segmentsize;
        bs = (segments[(i + 1) % setsegments % nsegments][2] - b) / segmentsize;
        for (y = 0; y < segmentsize; y++) {
            palette.push([Math.floor(r), Math.floor(g), Math.floor(b)]);
            r += rs;
            g += gs;
            b += bs;
        }
    }

    return palette;
};

var fractal = {
    symmetry: {x: null, y: 0 },
    region: {
        center: { x: -0.75, y: 0.0 },
        radius: { x: 2.5, y : 2.5 },
        angle: 0
    },
    formula: function(palette, zr, zi, cr, ci) {
        var maxiter = 128,
            bailout = 4,
            i = maxiter;

        while (i--) {
            var zr2 = zr * zr;
            var zi2 = zi * zi;

            if (zr2 + zi2 > bailout) {
                return palette[(maxiter - i) % palette.length];
            }

            zi = ci + (2 * zr * zi);
            zr = cr + zr2 - zi2;
        }

        return palette[0];
    },
    palette: xaos.makePalette()
};

xaos.zoom(document.getElementById("canvas"), fractal);
