//Santiago Arroyo Lozano - 317150700
function dibujar() {
    var canvas = document.querySelector('canvas');
    var context = canvas.getContext("2d");
    context.clearRect(0, 0, canvas.width, canvas.height);

    var r = parseFloat(document.getElementById("r").value);
    var k = parseFloat(document.getElementById("k").value);
    var vueltas = parseInt(document.getElementById("vueltas").value);

    context.setLineDash([5, 5]);
    context.beginPath();
    context.moveTo(canvas.width / 2, 0);
    context.lineTo(canvas.width / 2, canvas.height);
    context.moveTo(0, canvas.height / 2);
    context.lineTo(canvas.width, canvas.height / 2);
    context.stroke();

    context.setLineDash([]);
    context.beginPath();
    for (var t = 0; t <= 2 * Math.PI * vueltas; t += 0.01) {
        var x = r * (k + 1) * Math.cos(t) - r * Math.cos((k+1)*t);
        var y = r * (k + 1) * Math.sin(t) - r * Math.sin((k+1)*t);
        //Centramos
        x = canvas.width / 2 + x;
        y = canvas.height / 2 - y; 
        if (t === 0) context.moveTo(x, y);
        else context.lineTo(x, y);
    }
    context.stroke();
}