window.addEventListener('load', function(evt) {

    let canvas = this.document.getElementById('canvas_id');
    let context = canvas.getContext('2d');

    // Eje Y
    context.beginPath();
    context.strokeStyle = 'green';
    context.fillWidth = 10;
    context.lineCap = 'butt';
    context.setLineDash([10, 10]);
    context.moveTo(400, 10);
    context.lineTo(400, 600-10);
    
    // Eje X
    context.moveTo(10, 300);
    context.lineTo(800-10, 300);
    context.stroke();

    // Parámetros
    // https://en.wikipedia.org/wiki/Rose_(mathematics)#/media/File:Rose-rhodonea-curve-7x9-chart-improved.svg

    let n = 5;
    let d = 4;
    let k = n/d;
    let a = 100;

    // Valores para centrar
    let axisX = canvas.width/2;
    let axisY = canvas.height/2;

    
    context.beginPath();
    context.setLineDash([])

    context.strokeStyle = 'black';
    context.lineJoin = 'bevel';

    for (t = 0; t < 8*Math.PI; t+=0.01){

        /*
         * x = a cos(k*thetha)*cos(theta)
         * y = a cos(k*thetha)*sin(theta)
         */

        context.lineTo(
            axisX + 
        (a*Math.cos(k*t)*Math.cos(t)), 
            axisY + 
        (a*Math.cos(k*t)*Math.sin(t)));

    }
    context.stroke();
});